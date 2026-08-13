[CmdletBinding()]
param(
    [string]$Module = 'Fuglede.Z180K30ExceptionalProjectiveCap20PilotV89',
    [ValidateSet('build', 'checker')]
    [string]$Phase = 'build',
    [uint64]$MemoryCapBytes = 3489660928
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$lakeExe = Join-Path $workspaceRoot 'lean_agent\toolchains\bin\lake.exe'
$safeModule = $Module -replace '[^A-Za-z0-9_.-]', '_'
$telemetryStem = "$safeModule.$Phase"
$telemetryPath = Join-Path $workspaceRoot "audit\z180_k30_projective_v89_batch\$telemetryStem.json"
$stdoutPath = Join-Path $workspaceRoot "audit\z180_k30_projective_v89_batch\$telemetryStem.out.log"
$stderrPath = Join-Path $workspaceRoot "audit\z180_k30_projective_v89_batch\$telemetryStem.err.log"

$active = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe')
})
if ($active.Count -ne 0) {
    throw 'Serial window is not free for the isolated cap-20 pilot.'
}

$stdoutStream = [System.IO.File]::Open(
    $stdoutPath, [System.IO.FileMode]::Create,
    [System.IO.FileAccess]::Write, [System.IO.FileShare]::Read
)
$stderrStream = [System.IO.File]::Open(
    $stderrPath, [System.IO.FileMode]::Create,
    [System.IO.FileAccess]::Write, [System.IO.FileShare]::Read
)
$startInfo = [System.Diagnostics.ProcessStartInfo]::new()
$startInfo.FileName = $lakeExe
$startInfo.Arguments = if ($Phase -eq 'build') {
    "build $Module"
} else {
    "env leanchecker -v $Module"
}
$startInfo.WorkingDirectory = $leanRoot
$startInfo.UseShellExecute = $false
$startInfo.CreateNoWindow = $true
$startInfo.RedirectStandardOutput = $true
$startInfo.RedirectStandardError = $true
$process = [System.Diagnostics.Process]::new()
$process.StartInfo = $startInfo
if (-not $process.Start()) {
    throw "Failed to start isolated $Phase for $Module."
}
$stdoutCopy = $process.StandardOutput.BaseStream.CopyToAsync($stdoutStream)
$stderrCopy = $process.StandardError.BaseStream.CopyToAsync($stderrStream)

$ownIds = [System.Collections.Generic.HashSet[int]]::new()
[void]$ownIds.Add([int]$process.Id)
[uint64]$maxLeanWorkingSet = 0
$stopReason = $null
$stopDetail = $null

function Expand-OwnIds {
    param([object[]]$AllProcesses)
    do {
        $added = $false
        foreach ($candidate in $AllProcesses) {
            if ($ownIds.Contains([int]$candidate.ParentProcessId) -and
                -not $ownIds.Contains([int]$candidate.ProcessId)) {
                [void]$ownIds.Add([int]$candidate.ProcessId)
                $added = $true
            }
        }
    } while ($added)
}

while (-not $process.WaitForExit(250)) {
    $all = @(Get-CimInstance Win32_Process)
    Expand-OwnIds -AllProcesses $all
    foreach ($candidate in $all) {
        $candidateId = [int]$candidate.ProcessId
        if ($ownIds.Contains($candidateId) -and
            $candidate.Name -in @('lean.exe', 'leanchecker.exe')) {
            [uint64]$workingSet = $candidate.WorkingSetSize
            if ($workingSet -gt $maxLeanWorkingSet) {
                $maxLeanWorkingSet = $workingSet
            }
            if ($workingSet -gt $memoryCapBytes) {
                $stopReason = 'memory-cap'
                $stopDetail = "$($candidate.Name) PID $candidateId reached $workingSet bytes"
                break
            }
        }
    }
    if ($null -eq $stopReason) {
        $foreign = @($all | Where-Object {
            $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe') -and
            -not $ownIds.Contains([int]$_.ProcessId)
        })
        if ($foreign.Count -gt 0) {
            $stopReason = 'foreign-conflict'
            $stopDetail = ($foreign | ForEach-Object {
                '{0}:{1}' -f $_.Name, $_.ProcessId
            }) -join ', '
        }
    }
    if ($null -ne $stopReason) {
        $all = @(Get-CimInstance Win32_Process)
        Expand-OwnIds -AllProcesses $all
        foreach ($target in ($all | Where-Object {
            $ownIds.Contains([int]$_.ProcessId)
        } | Sort-Object ProcessId -Descending)) {
            Stop-Process -Id ([int]$target.ProcessId) -Force -ErrorAction SilentlyContinue
        }
        break
    }
}

$process.WaitForExit()
[System.Threading.Tasks.Task]::WaitAll(@($stdoutCopy, $stderrCopy))
$stdoutStream.Dispose()
$stderrStream.Dispose()
$exitCode = [int]$process.ExitCode
$status = if ($null -ne $stopReason) {
    $stopReason
} elseif ($exitCode -eq 0) {
    'passed'
} else {
    'failed'
}
$telemetry = [ordered]@{
    module = $Module
    phase = $Phase
    status = $status
    capBytes = $MemoryCapBytes
    maxLeanWorkingSetBytes = $maxLeanWorkingSet
    exitCode = $exitCode
    detail = $stopDetail
    completedAtUtc = [DateTime]::UtcNow.ToString('o')
    stdoutPath = $stdoutPath
    stderrPath = $stderrPath
}
$telemetry | ConvertTo-Json -Depth 4 | Set-Content -LiteralPath $telemetryPath -Encoding UTF8
$telemetry | ConvertTo-Json -Compress
if ($status -ne 'passed') {
    exit 1
}
