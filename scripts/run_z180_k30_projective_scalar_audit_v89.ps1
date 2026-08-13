[CmdletBinding()]
param(
    [int]$PollMilliseconds = 250,
    [int]$WindowPollSeconds = 5
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$lakeExe = Join-Path $workspaceRoot 'lean_agent\toolchains\bin\lake.exe'
$generatorPath = Join-Path $scriptRoot 'generate_z180_k30_projective_scalar_audit_v89.py'
$manifestPath = Join-Path $scriptRoot 'z180_k30_projective_scalar_audit_v89.manifest.json'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_v89_batch'
$logRoot = Join-Path $auditRoot 'logs'
$statePath = Join-Path $auditRoot 'state.json'
$pauseRequestPath = Join-Path $auditRoot 'pause.request'

if (-not (Test-Path -LiteralPath $lakeExe -PathType Leaf)) {
    throw "Lake executable not found: $lakeExe"
}
if (-not (Test-Path -LiteralPath $generatorPath -PathType Leaf)) {
    throw "Generator not found: $generatorPath"
}
if (-not (Test-Path -LiteralPath $manifestPath -PathType Leaf)) {
    throw "Manifest not found: $manifestPath"
}

New-Item -ItemType Directory -Path $logRoot -Force | Out-Null

$leanProcessNames = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::OrdinalIgnoreCase
)
foreach ($name in @('lake.exe', 'lean.exe', 'leanchecker.exe')) {
    [void]$leanProcessNames.Add($name)
}

function Get-LeanFamilyProcesses {
    @(Get-CimInstance Win32_Process -ErrorAction Stop | Where-Object {
        $leanProcessNames.Contains([string]$_.Name)
    })
}

function Wait-SerialWindow {
    param([string]$Reason)

    $lastReport = [DateTime]::MinValue
    while ($true) {
        $active = @(Get-LeanFamilyProcesses)
        if ($active.Count -eq 0) {
            return
        }
        $now = [DateTime]::UtcNow
        if (($now - $lastReport).TotalSeconds -ge 30) {
            $description = ($active | ForEach-Object {
                '{0}:{1}' -f $_.Name, $_.ProcessId
            }) -join ', '
            Write-Host ("WAIT serial-window ({0}): {1}" -f $Reason, $description)
            $lastReport = $now
        }
        Start-Sleep -Seconds $WindowPollSeconds
    }
}

function Expand-OwnProcessIds {
    param(
        [System.Collections.Generic.HashSet[int]]$OwnIds,
        [object[]]$AllProcesses
    )

    do {
        $added = $false
        foreach ($candidate in $AllProcesses) {
            $pidValue = [int]$candidate.ProcessId
            $parentValue = [int]$candidate.ParentProcessId
            if ($OwnIds.Contains($parentValue) -and -not $OwnIds.Contains($pidValue)) {
                [void]$OwnIds.Add($pidValue)
                $added = $true
            }
        }
    } while ($added)
}

function Stop-OwnProcessTree {
    param([System.Collections.Generic.HashSet[int]]$OwnIds)

    $all = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue)
    Expand-OwnProcessIds -OwnIds $OwnIds -AllProcesses $all
    $targets = @($all | Where-Object { $OwnIds.Contains([int]$_.ProcessId) })

    # Stop descendants before the root. Only PIDs proven to descend from the
    # process started by this script are eligible.
    foreach ($target in ($targets | Sort-Object ProcessId -Descending)) {
        Stop-Process -Id ([int]$target.ProcessId) -Force -ErrorAction SilentlyContinue
    }
}

function Invoke-MonitoredLake {
    param(
        [string]$Module,
        [ValidateSet('build', 'checker')]
        [string]$Phase,
        [uint64]$MemoryCapBytes,
        [int]$Attempt
    )

    $safeModule = $Module -replace '[^A-Za-z0-9_.-]', '_'
    $stdoutPath = Join-Path $logRoot ("{0}.{1}.{2}.out.log" -f $safeModule, $Phase, $Attempt)
    $stderrPath = Join-Path $logRoot ("{0}.{1}.{2}.err.log" -f $safeModule, $Phase, $Attempt)
    if ($Phase -eq 'build') {
        $arguments = @('build', $Module)
    }
    else {
        $arguments = @('env', 'leanchecker', '-v', $Module)
    }

    Wait-SerialWindow -Reason "$Phase $Module"
    Write-Host ("START {0} {1} attempt={2}" -f $Phase, $Module, $Attempt)
    $stdoutStream = [System.IO.File]::Open(
        $stdoutPath,
        [System.IO.FileMode]::Create,
        [System.IO.FileAccess]::Write,
        [System.IO.FileShare]::Read
    )
    $stderrStream = [System.IO.File]::Open(
        $stderrPath,
        [System.IO.FileMode]::Create,
        [System.IO.FileAccess]::Write,
        [System.IO.FileShare]::Read
    )
    $startInfo = [System.Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $lakeExe
    $startInfo.WorkingDirectory = $leanRoot
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    foreach ($argument in $arguments) {
        if ($argument -match '[\s"]') {
            $stdoutStream.Dispose()
            $stderrStream.Dispose()
            throw "Unsafe lake argument for the PowerShell 5 runner: $argument"
        }
    }
    $startInfo.Arguments = $arguments -join ' '
    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    if (-not $process.Start()) {
        $stdoutStream.Dispose()
        $stderrStream.Dispose()
        throw "Failed to start owned $Phase process for $Module."
    }
    $stdoutCopy = $process.StandardOutput.BaseStream.CopyToAsync($stdoutStream)
    $stderrCopy = $process.StandardError.BaseStream.CopyToAsync($stderrStream)

    $ownIds = [System.Collections.Generic.HashSet[int]]::new()
    [void]$ownIds.Add([int]$process.Id)
    [uint64]$maxLeanWorkingSet = 0
    $stopReason = $null
    $stopDetail = $null

    while (-not $process.WaitForExit($PollMilliseconds)) {
        $all = @(Get-CimInstance Win32_Process -ErrorAction Stop)
        Expand-OwnProcessIds -OwnIds $ownIds -AllProcesses $all

        foreach ($candidate in $all) {
            $candidateId = [int]$candidate.ProcessId
            $candidateName = [string]$candidate.Name
            $isCheckedWorker =
                $candidateName.Equals('lean.exe', [System.StringComparison]::OrdinalIgnoreCase) -or
                $candidateName.Equals('leanchecker.exe', [System.StringComparison]::OrdinalIgnoreCase)
            if ($ownIds.Contains($candidateId) -and $isCheckedWorker) {
                $workingSet = [uint64]$candidate.WorkingSetSize
                if ($workingSet -gt $maxLeanWorkingSet) {
                    $maxLeanWorkingSet = $workingSet
                }
                if ($workingSet -gt $MemoryCapBytes) {
                    $stopReason = 'memory-cap'
                    $stopDetail = "$candidateName PID $candidateId reached $workingSet bytes"
                    break
                }
            }
        }

        if ($null -eq $stopReason) {
            $foreign = @($all | Where-Object {
                $leanProcessNames.Contains([string]$_.Name) -and
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
            Stop-OwnProcessTree -OwnIds $ownIds
            break
        }
    }

    $process.WaitForExit()
    [System.Threading.Tasks.Task]::WaitAll(@($stdoutCopy, $stderrCopy))
    $stdoutStream.Dispose()
    $stderrStream.Dispose()
    $exitCode = [int]$process.ExitCode
    if ($null -ne $stopReason) {
        Write-Host ("STOP {0} {1} reason={2} detail={3} maxLeanWS={4}" -f `
            $Phase, $Module, $stopReason, $stopDetail, $maxLeanWorkingSet)
        return [pscustomobject]@{
            status = $stopReason
            exitCode = $exitCode
            maxLeanWorkingSetBytes = $maxLeanWorkingSet
            stdoutPath = $stdoutPath
            stderrPath = $stderrPath
            detail = $stopDetail
        }
    }

    if ($exitCode -ne 0) {
        Write-Host ("FAIL {0} {1} exit={2} maxLeanWS={3}" -f `
            $Phase, $Module, $exitCode, $maxLeanWorkingSet)
        return [pscustomobject]@{
            status = 'failed'
            exitCode = $exitCode
            maxLeanWorkingSetBytes = $maxLeanWorkingSet
            stdoutPath = $stdoutPath
            stderrPath = $stderrPath
            detail = 'nonzero exit code'
        }
    }

    Write-Host ("PASS {0} {1} maxLeanWS={2}" -f $Phase, $Module, $maxLeanWorkingSet)
    [pscustomobject]@{
        status = 'passed'
        exitCode = 0
        maxLeanWorkingSetBytes = $maxLeanWorkingSet
        stdoutPath = $stdoutPath
        stderrPath = $stderrPath
        detail = $null
    }
}

function Invoke-PhaseWithConflictRetry {
    param(
        [string]$Module,
        [ValidateSet('build', 'checker')]
        [string]$Phase,
        [uint64]$MemoryCapBytes
    )

    $attempt = 1
    while ($true) {
        $result = Invoke-MonitoredLake `
            -Module $Module `
            -Phase $Phase `
            -MemoryCapBytes $MemoryCapBytes `
            -Attempt $attempt
        if ($result.status -eq 'foreign-conflict') {
            Write-Host ("RETRY {0} {1} after foreign process clears" -f $Phase, $Module)
            $attempt += 1
            continue
        }
        return $result
    }
}

function Save-State {
    param(
        [string]$ManifestSha256,
        [System.Collections.Generic.HashSet[string]]$Completed,
        [System.Collections.ArrayList]$Records,
        [string]$StartedAtUtc
    )

    $state = [ordered]@{
        schema = 'z180-k30-projective-v89-serial-state-v1'
        manifestSha256 = $ManifestSha256
        startedAtUtc = $StartedAtUtc
        updatedAtUtc = [DateTime]::UtcNow.ToString('o')
        completedModules = @($Completed | Sort-Object)
        records = @($Records)
    }
    $temporaryStatePath = "$statePath.tmp"
    $state | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $temporaryStatePath -Encoding UTF8
    Move-Item -LiteralPath $temporaryStatePath -Destination $statePath -Force
}

Wait-SerialWindow -Reason 'generator authentication'
Write-Host 'AUTH generator/manifest/generated sources'
& python $generatorPath
if ($LASTEXITCODE -ne 0) {
    throw "Generator authentication failed with exit code $LASTEXITCODE"
}

$manifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$plan = $manifest.serialReplayPlan
$memoryCapBytes = [uint64]$plan.memoryCapBytesPerLean
if ([int]$plan.maxConcurrentLeanProcesses -ne 1) {
    throw 'Manifest does not require exactly one concurrent Lean process.'
}
if ($plan.buildOnlyLeafModules -ne $true) {
    throw 'Manifest does not authenticate the build-only finite-leaf policy.'
}
$manifestSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()

$completed = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$records = [System.Collections.ArrayList]::new()
$startedAtUtc = [DateTime]::UtcNow.ToString('o')

if (Test-Path -LiteralPath $statePath -PathType Leaf) {
    $existingState = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
    if ([string]$existingState.manifestSha256 -eq $manifestSha256) {
        foreach ($module in @($existingState.completedModules)) {
            [void]$completed.Add([string]$module)
        }
        foreach ($record in @($existingState.records)) {
            [void]$records.Add($record)
        }
        $startedAtUtc = [string]$existingState.startedAtUtc
        Write-Host ("RESUME completed={0}" -f $completed.Count)
    }
    else {
        Write-Host 'RESET stale state: manifest digest changed'
    }
}

$orderedModules = [System.Collections.ArrayList]::new()
$seenModules = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$buildOnlyModules = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
function Add-OrderedModule {
    param([string]$Module)
    if ($seenModules.Add($Module)) {
        [void]$orderedModules.Add($Module)
    }
}

# The refined interface and the two cap-20 pilots are always first. The pilot
# leaves also occur in the authenticated leaf plan and are deduplicated here.
# D3B000 is the cap-10 replacement for the exact cap-20 leaf that triggered
# the fail-closed memory stop, so it is replayed before the already-sealed
# d=4 and d=6 pilots.
foreach ($module in @(
    'Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89',
    'Fuglede.Z180K30ExceptionalProjectiveLiteralAuditV89',
    'Fuglede.Z180K30ExceptionalProjectiveScalarV89D3B000',
    'Fuglede.Z180K30ExceptionalProjectiveScalarV89D4B062',
    'Fuglede.Z180K30ExceptionalProjectiveScalarV89D6B014'
)) {
    Add-OrderedModule -Module $module
}
foreach ($batch in @($plan.leafBatches)) {
    foreach ($module in @($batch)) {
        $leafModule = [string]$module
        Add-OrderedModule -Module $leafModule
        [void]$buildOnlyModules.Add($leafModule)
    }
}
foreach ($module in @($plan.dataModules)) {
    Add-OrderedModule -Module ([string]$module)
}
foreach ($batch in @($plan.rowBatches)) {
    foreach ($module in @($batch)) {
        Add-OrderedModule -Module ([string]$module)
    }
}
foreach ($module in @($plan.divisorModules)) {
    Add-OrderedModule -Module ([string]$module)
}
Add-OrderedModule -Module ([string]$plan.bridgeModule)
Add-OrderedModule -Module ([string]$plan.finalModule)

Write-Host ("PLAN modules={0} completed={1} capBytes={2}" -f `
    $orderedModules.Count, $completed.Count, $memoryCapBytes)

$ordinal = 0
foreach ($moduleObject in $orderedModules) {
    $ordinal += 1
    $module = [string]$moduleObject
    if ($completed.Contains($module)) {
        Write-Host ("SKIP [{0}/{1}] {2}" -f $ordinal, $orderedModules.Count, $module)
        continue
    }

    Write-Host ("MODULE [{0}/{1}] {2}" -f $ordinal, $orderedModules.Count, $module)
    $build = Invoke-PhaseWithConflictRetry `
        -Module $module -Phase build -MemoryCapBytes $memoryCapBytes
    if ($build.status -ne 'passed') {
        [void]$records.Add([pscustomobject]@{
            module = $module
            phase = 'build'
            status = $build.status
            atUtc = [DateTime]::UtcNow.ToString('o')
            maxLeanWorkingSetBytes = $build.maxLeanWorkingSetBytes
            detail = $build.detail
            stdoutPath = $build.stdoutPath
            stderrPath = $build.stderrPath
        })
        Save-State -ManifestSha256 $manifestSha256 -Completed $completed `
            -Records $records -StartedAtUtc $startedAtUtc
        throw "Fail-closed build stop for $module ($($build.status)): $($build.detail)"
    }

    $checker = $null
    if (-not $buildOnlyModules.Contains($module)) {
        $checker = Invoke-PhaseWithConflictRetry `
            -Module $module -Phase checker -MemoryCapBytes $memoryCapBytes
        if ($checker.status -ne 'passed') {
            [void]$records.Add([pscustomobject]@{
                module = $module
                phase = 'checker'
                status = $checker.status
                atUtc = [DateTime]::UtcNow.ToString('o')
                maxLeanWorkingSetBytes = $checker.maxLeanWorkingSetBytes
                detail = $checker.detail
                stdoutPath = $checker.stdoutPath
                stderrPath = $checker.stderrPath
            })
            Save-State -ManifestSha256 $manifestSha256 -Completed $completed `
                -Records $records -StartedAtUtc $startedAtUtc
            throw "Fail-closed checker stop for $module ($($checker.status)): $($checker.detail)"
        }
    }

    [void]$completed.Add($module)
    [void]$records.Add([pscustomobject]@{
        module = $module
        phase = 'sealed'
        status = 'passed'
        atUtc = [DateTime]::UtcNow.ToString('o')
        buildMaxLeanWorkingSetBytes = $build.maxLeanWorkingSetBytes
        checkerPolicy = if ($null -eq $checker) { 'transitive-root' } else { 'individual' }
        checkerMaxLeanWorkingSetBytes = if ($null -eq $checker) { $null } else {
            $checker.maxLeanWorkingSetBytes
        }
        buildStdoutPath = $build.stdoutPath
        buildStderrPath = $build.stderrPath
        checkerStdoutPath = if ($null -eq $checker) { $null } else { $checker.stdoutPath }
        checkerStderrPath = if ($null -eq $checker) { $null } else { $checker.stderrPath }
    })
    Save-State -ManifestSha256 $manifestSha256 -Completed $completed `
        -Records $records -StartedAtUtc $startedAtUtc
    Write-Host ("SEALED [{0}/{1}] {2}" -f $ordinal, $orderedModules.Count, $module)
    if (Test-Path -LiteralPath $pauseRequestPath -PathType Leaf) {
        Remove-Item -LiteralPath $pauseRequestPath -Force
        Write-Host ("PAUSED clean-boundary completed={0}" -f $completed.Count)
        exit 0
    }
}

Write-Host ("COMPLETE modules={0} manifestSha256={1}" -f `
    $completed.Count, $manifestSha256)

