param(
  [double]$MemoryLimitGiB = 2.5,
  [int]$PollMilliseconds = 200,
  [int]$CommandTimeoutMinutes = 30,
  [string]$StatePath = '',
  [switch]$Restart
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$workspace = (Resolve-Path $PSScriptRoot).Path
$manifestPath = Join-Path $workspace 'Fuglede\Z180K30ExceptionalFramedCandidateExtractionV95.manifest.json'
$verifierPath = Join-Path $workspace 'Verify-Z180K30FramedCandidateExtractionV95.ps1'
$lakePath = (Resolve-Path (Join-Path $workspace '..\lean_agent\toolchains\bin\lake.exe')).Path
$checkerPath = (Resolve-Path (Join-Path $workspace '..\lean_agent\toolchains\bin\leanchecker.exe')).Path
$logRoot = Join-Path $workspace '.v95-serial-logs'
if ([string]::IsNullOrWhiteSpace($StatePath)) {
  $StatePath = Join-Path $workspace 'Z180K30ExceptionalFramedCandidateExtractionV95.serial-state.json'
} elseif (-not [IO.Path]::IsPathRooted($StatePath)) {
  $StatePath = Join-Path $workspace $StatePath
}
$lockPath = "$StatePath.lock"
$memoryLimitBytes = [uint64][Math]::Floor($MemoryLimitGiB * 1GB)
$commandTimeout = [TimeSpan]::FromMinutes($CommandTimeoutMinutes)

if ($memoryLimitBytes -lt 512MB) { throw 'MemoryLimitGiB must be at least 0.5.' }
if ($PollMilliseconds -lt 50 -or $PollMilliseconds -gt 5000) {
  throw 'PollMilliseconds must be between 50 and 5000.'
}
if ($CommandTimeoutMinutes -lt 1) { throw 'CommandTimeoutMinutes must be positive.' }

if (-not ('V95Serial.JobMemoryCap' -as [type])) {
  Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.Runtime.InteropServices;
using System.Threading;

namespace V95Serial {
  [StructLayout(LayoutKind.Sequential)]
  internal struct IO_COUNTERS {
    public UInt64 ReadOperationCount;
    public UInt64 WriteOperationCount;
    public UInt64 OtherOperationCount;
    public UInt64 ReadTransferCount;
    public UInt64 WriteTransferCount;
    public UInt64 OtherTransferCount;
  }

  [StructLayout(LayoutKind.Sequential)]
  internal struct JOBOBJECT_BASIC_LIMIT_INFORMATION {
    public Int64 PerProcessUserTimeLimit;
    public Int64 PerJobUserTimeLimit;
    public UInt32 LimitFlags;
    public UIntPtr MinimumWorkingSetSize;
    public UIntPtr MaximumWorkingSetSize;
    public UInt32 ActiveProcessLimit;
    public UIntPtr Affinity;
    public UInt32 PriorityClass;
    public UInt32 SchedulingClass;
  }

  [StructLayout(LayoutKind.Sequential)]
  internal struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
    public JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
    public IO_COUNTERS IoInfo;
    public UIntPtr ProcessMemoryLimit;
    public UIntPtr JobMemoryLimit;
    public UIntPtr PeakProcessMemoryUsed;
    public UIntPtr PeakJobMemoryUsed;
  }

  public sealed class JobMemoryCap : IDisposable {
    private const UInt32 JOB_OBJECT_LIMIT_JOB_MEMORY = 0x00000200;
    private const UInt32 JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000;
    private IntPtr handle;

    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
    private static extern IntPtr CreateJobObject(IntPtr attributes, string name);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool SetInformationJobObject(
      IntPtr job, int infoClass, IntPtr info, UInt32 length);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool CloseHandle(IntPtr handle);

    public JobMemoryCap(UInt64 bytes) {
      handle = CreateJobObject(IntPtr.Zero, null);
      if (handle == IntPtr.Zero) throw new Win32Exception();
      var limits = new JOBOBJECT_EXTENDED_LIMIT_INFORMATION();
      limits.BasicLimitInformation.LimitFlags =
        JOB_OBJECT_LIMIT_JOB_MEMORY | JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
      limits.JobMemoryLimit = (UIntPtr)bytes;
      int size = Marshal.SizeOf(typeof(JOBOBJECT_EXTENDED_LIMIT_INFORMATION));
      IntPtr buffer = Marshal.AllocHGlobal(size);
      try {
        Marshal.StructureToPtr(limits, buffer, false);
        if (!SetInformationJobObject(handle, 9, buffer, (UInt32)size)) {
          throw new Win32Exception();
        }
      } catch {
        CloseHandle(handle);
        handle = IntPtr.Zero;
        throw;
      } finally {
        Marshal.FreeHGlobal(buffer);
      }
    }

    public void AddProcess(IntPtr processHandle) {
      if (handle == IntPtr.Zero) throw new ObjectDisposedException("JobMemoryCap");
      if (!AssignProcessToJobObject(handle, processHandle)) {
        throw new Win32Exception();
      }
    }

    public void Dispose() {
      IntPtr oldHandle = Interlocked.Exchange(ref handle, IntPtr.Zero);
      if (oldHandle != IntPtr.Zero) CloseHandle(oldHandle);
    }
  }
}
'@
}

function Get-Sha256Lower([string]$Path) {
  return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
}

function Convert-SourcePathToModule([string]$Path) {
  if (-not $Path.EndsWith('.lean', [StringComparison]::Ordinal)) {
    throw "Manifest source is not a Lean file: $Path"
  }
  return $Path.Substring(0, $Path.Length - 5).Replace('/', '.').Replace('\', '.')
}

function Get-OleanPath([string]$Module) {
  $relative = $Module.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.olean'
  return Join-Path $workspace (Join-Path '.lake\build\lib\lean' $relative)
}

function Get-WorkspaceRelativePath([string]$Path) {
  $fullPath = [IO.Path]::GetFullPath($Path)
  $prefix = $workspace.TrimEnd([IO.Path]::DirectorySeparatorChar) +
    [IO.Path]::DirectorySeparatorChar
  if (-not $fullPath.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Path is outside the workspace: $fullPath"
  }
  return $fullPath.Substring($prefix.Length).Replace('\', '/')
}

function Save-State([System.Collections.IDictionary]$State) {
  $parent = Split-Path -Parent $StatePath
  if (-not (Test-Path -LiteralPath $parent -PathType Container)) {
    New-Item -ItemType Directory -Path $parent | Out-Null
  }
  $temporary = "$StatePath.tmp.$PID"
  $json = $State | ConvertTo-Json -Depth 8
  [IO.File]::WriteAllText($temporary, $json + [Environment]::NewLine,
    [Text.UTF8Encoding]::new($false))
  Move-Item -LiteralPath $temporary -Destination $StatePath -Force
}

function Get-ProcessTreeWorkingSet([int]$RootPid) {
  $rows = @(Get-CimInstance Win32_Process |
    Select-Object ProcessId, ParentProcessId, WorkingSetSize)
  $ids = [System.Collections.Generic.HashSet[uint32]]::new()
  [void]$ids.Add([uint32]$RootPid)
  $changed = $true
  while ($changed) {
    $changed = $false
    foreach ($row in $rows) {
      if ($ids.Contains([uint32]$row.ParentProcessId) -and
          $ids.Add([uint32]$row.ProcessId)) {
        $changed = $true
      }
    }
  }
  [uint64]$total = 0
  foreach ($row in $rows) {
    if ($ids.Contains([uint32]$row.ProcessId)) {
      $total += [uint64]$row.WorkingSetSize
    }
  }
  return $total
}

function Get-LogTail([string]$Path, [int]$Count = 80) {
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) { return '' }
  return ((Get-Content -LiteralPath $Path -Tail $Count) -join [Environment]::NewLine)
}

function Invoke-CappedProcess(
    [string]$Label,
    [string[]]$Arguments,
    [string]$StdoutPath,
    [string]$StderrPath) {
  $job = [V95Serial.JobMemoryCap]::new($memoryLimitBytes)
  $process = $null
  $jobDisposed = $false
  [uint64]$peakWorkingSet = 0
  $stopwatch = [Diagnostics.Stopwatch]::StartNew()
  $limitReason = $null
  try {
    $process = Start-Process -FilePath $lakePath -ArgumentList $Arguments `
      -WorkingDirectory $workspace -WindowStyle Hidden -PassThru `
      -RedirectStandardOutput $StdoutPath -RedirectStandardError $StderrPath
    try {
      $job.AddProcess($process.Handle)
    } catch {
      Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
      throw "Could not place '$Label' in the hard-cap job object: $($_.Exception.Message)"
    }

    while (-not $process.HasExited) {
      Start-Sleep -Milliseconds $PollMilliseconds
      $workingSet = Get-ProcessTreeWorkingSet $process.Id
      if ($workingSet -gt $peakWorkingSet) { $peakWorkingSet = $workingSet }
      if ($workingSet -ge $memoryLimitBytes) {
        $limitReason = "process tree working set reached $workingSet bytes"
        $job.Dispose()
        $jobDisposed = $true
        break
      }
      if ($stopwatch.Elapsed -ge $commandTimeout) {
        $limitReason = "command exceeded $CommandTimeoutMinutes minutes"
        $job.Dispose()
        $jobDisposed = $true
        break
      }
      $process.Refresh()
    }
    if ($null -ne $limitReason) {
      try { $process.WaitForExit(10000) | Out-Null } catch {}
      throw "$Label fail-stop: $limitReason"
    }
    $process.WaitForExit()
    return [pscustomobject]@{
      exit_code = $process.ExitCode
      peak_tree_working_set_bytes = $peakWorkingSet
      stdout = $StdoutPath
      stderr = $StderrPath
    }
  } finally {
    $stopwatch.Stop()
    if (-not $jobDisposed) { $job.Dispose() }
    if ($null -ne $process) { $process.Dispose() }
  }
}

$lockStream = $null
try {
  $lockParent = Split-Path -Parent $lockPath
  if (-not (Test-Path -LiteralPath $lockParent -PathType Container)) {
    New-Item -ItemType Directory -Path $lockParent | Out-Null
  }
  try {
    $lockStream = [IO.File]::Open($lockPath, [IO.FileMode]::OpenOrCreate,
      [IO.FileAccess]::ReadWrite, [IO.FileShare]::None)
  } catch {
    throw "Another V95 serial runner holds $lockPath"
  }
  $lockStream.SetLength(0)
  $lockBytes = [Text.Encoding]::UTF8.GetBytes("PID=$PID`n")
  $lockStream.Write($lockBytes, 0, $lockBytes.Length)
  $lockStream.Flush()

  & $verifierPath
  if ($LASTEXITCODE -ne 0) { throw 'Fail-closed source verification failed.' }

  $activeLean = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -match '^(lean|lake|leanchecker)\.exe$'
  })
  if ($activeLean.Count -ne 0) {
    $activeSummary = ($activeLean | ForEach-Object {
      "$($_.Name):$($_.ProcessId)"
    }) -join ', '
    throw "Serial ownership preflight failed; active processes: $activeSummary"
  }

  New-Item -ItemType Directory -Force -Path $logRoot | Out-Null
  $manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
  $manifestHash = Get-Sha256Lower $manifestPath
  $sourcesByPath = @{}
  foreach ($source in $manifest.sources) { $sourcesByPath[$source.path] = $source }

  if ($Restart -and (Test-Path -LiteralPath $StatePath -PathType Leaf)) {
    $archive = "$StatePath.restart.$([DateTime]::UtcNow.ToString('yyyyMMddTHHmmssZ'))"
    Move-Item -LiteralPath $StatePath -Destination $archive
  }

  $completed = @()
  if (Test-Path -LiteralPath $StatePath -PathType Leaf) {
    $loaded = Get-Content -LiteralPath $StatePath -Raw | ConvertFrom-Json
    if ($loaded.schema -cne 'z180-k30-framed-candidate-serial-state/v1') {
      throw "Unexpected state schema in $StatePath"
    }
    if ($loaded.manifest_sha256 -cne $manifestHash) {
      throw 'State manifest hash differs; use -Restart only after reviewing the changed manifest.'
    }
    if ([uint64]$loaded.memory_limit_bytes -ne $memoryLimitBytes) {
      throw 'State memory limit differs; resume with the original MemoryLimitGiB or use -Restart.'
    }
    $completed = @($loaded.completed)
  }

  if ($completed.Count -gt $manifest.build_order.Count) {
    throw 'State contains more completed modules than the manifest.'
  }
  for ($index = 0; $index -lt $completed.Count; $index++) {
    $entry = $completed[$index]
    $expectedPath = [string]$manifest.build_order[$index]
    $expectedModule = Convert-SourcePathToModule $expectedPath
    if ([int]$entry.index -ne $index -or
        $entry.path -cne $expectedPath -or
        $entry.module -cne $expectedModule -or
        $entry.source_sha256 -cne $sourcesByPath[$expectedPath].sha256 -or
        $entry.checker_passed -ne $true) {
      throw "State is not an authenticated manifest prefix at index $index."
    }
    $sourcePath = Join-Path $workspace ($expectedPath.Replace('/', '\'))
    if ((Get-Sha256Lower $sourcePath) -cne $entry.source_sha256) {
      throw "Completed source changed: $expectedPath"
    }
    $oleanPath = Get-OleanPath $expectedModule
    if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf) -or
        (Get-Sha256Lower $oleanPath) -cne $entry.olean_sha256) {
      throw "Authenticated olean missing or changed: $expectedModule"
    }
  }

  $state = [ordered]@{
    schema = 'z180-k30-framed-candidate-serial-state/v1'
    manifest_sha256 = $manifestHash
    memory_limit_bytes = $memoryLimitBytes
    command_timeout_minutes = $CommandTimeoutMinutes
    completed = @($completed)
    last_failure = $null
    updated_at_utc = [DateTime]::UtcNow.ToString('o')
  }
  Save-State $state

  Write-Output "RESUME authenticated=$($completed.Count) total=$($manifest.build_order.Count)"
  for ($index = $completed.Count; $index -lt $manifest.build_order.Count; $index++) {
    $path = [string]$manifest.build_order[$index]
    $module = Convert-SourcePathToModule $path
    $source = $sourcesByPath[$path]
    $stamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffZ')
    $safeModule = $module.Replace('.', '_')
    $buildOut = Join-Path $logRoot "$($index.ToString('00'))-$safeModule-$stamp.build.stdout.log"
    $buildErr = Join-Path $logRoot "$($index.ToString('00'))-$safeModule-$stamp.build.stderr.log"
    $checkOut = Join-Path $logRoot "$($index.ToString('00'))-$safeModule-$stamp.check.stdout.log"
    $checkErr = Join-Path $logRoot "$($index.ToString('00'))-$safeModule-$stamp.check.stderr.log"

    Write-Output "[$($index + 1)/$($manifest.build_order.Count)] BUILD $module"
    try {
      $build = Invoke-CappedProcess "build $module" @('build', $module) $buildOut $buildErr
      if ($build.exit_code -ne 0) {
        throw "build exited $($build.exit_code)`n$(Get-LogTail $buildErr)"
      }
      $oleanPath = Get-OleanPath $module
      if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
        throw "build produced no olean at $oleanPath"
      }

      Write-Output "[$($index + 1)/$($manifest.build_order.Count)] CHECK $module"
      $check = Invoke-CappedProcess "checker $module" `
        @('env', $checkerPath, '-v', $module) $checkOut $checkErr
      if ($check.exit_code -ne 0) {
        throw "checker exited $($check.exit_code)`n$(Get-LogTail $checkErr)"
      }

      $record = [ordered]@{
        index = $index
        path = $path
        module = $module
        source_sha256 = [string]$source.sha256
        olean_sha256 = Get-Sha256Lower $oleanPath
        checker_passed = $true
        build_peak_tree_working_set_bytes = $build.peak_tree_working_set_bytes
        checker_peak_tree_working_set_bytes = $check.peak_tree_working_set_bytes
        build_stdout = Get-WorkspaceRelativePath $buildOut
        build_stderr = Get-WorkspaceRelativePath $buildErr
        checker_stdout = Get-WorkspaceRelativePath $checkOut
        checker_stderr = Get-WorkspaceRelativePath $checkErr
        authenticated_at_utc = [DateTime]::UtcNow.ToString('o')
      }
      $state.completed = @($state.completed) + @($record)
      $state.last_failure = $null
      $state.updated_at_utc = [DateTime]::UtcNow.ToString('o')
      Save-State $state
      Write-Output "[$($index + 1)/$($manifest.build_order.Count)] PASS $module"
    } catch {
      $state.last_failure = [ordered]@{
        index = $index
        path = $path
        module = $module
        message = $_.Exception.Message
        failed_at_utc = [DateTime]::UtcNow.ToString('o')
      }
      $state.updated_at_utc = [DateTime]::UtcNow.ToString('o')
      Save-State $state
      throw
    }
  }

  Write-Output "PASS: authenticated build+checker replay for $($state.completed.Count) manifest modules"
} catch {
  [Console]::Error.WriteLine("FAIL: $($_.Exception.Message)")
  exit 1
} finally {
  if ($null -ne $lockStream) {
    $lockStream.Dispose()
    Remove-Item -LiteralPath $lockPath -Force -ErrorAction SilentlyContinue
  }
}
