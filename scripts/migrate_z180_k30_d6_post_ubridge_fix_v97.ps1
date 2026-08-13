param()

$ErrorActionPreference = 'Stop'

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_d6_algebraic_v97'
$statePath = Join-Path $auditRoot 'state.json'
$manifestPath = Join-Path $leanRoot 'generated\z180_k30_d6_algebraic_v97.manifest.json'
$generatorPath = Join-Path $leanRoot 'scripts\generate_z180_k30_d6_algebraic_v97.py'
$oldManifestPath = Join-Path $auditRoot `
    'manifest-migration-backup-6ea8f3c0d3384c4f9e18de47fb15fafb\planned-manifest.json'
$migrationPath = Join-Path $auditRoot 'post-ubridge-fix-migration.json'
$lockPath = Join-Path $auditRoot 'post-ubridge-fix-migration.lock'

$expectedOldStateSha = 'bb1d842f249477ff3dc1b5e47831b76307c4e4894250dff15ddf595f1b12bd74'
$expectedOldManifestSha = '57897ef2aea94300564858463113fa7eb0938fde314cbdbdef51c6eb66b6ded1'
$expectedNewManifestSha = '7c16fb75e67cb75a73ad8e5444c9bb3d9ba4875d466d416f5921f2300ae22cee'
$expectedGeneratorSha = '7f09165e287f1fb4b769d911ed59ed65205541ccc8019bf34d12fd95e18b451c'
$uBridgeModule = 'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97'
$uBridgeKey = 'Fuglede/Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97.lean'
$expectedBridgeSha = 'b394f2da9c175ad184c8be74043db9a28ad40886b20e4264a249413824477967'

function Get-LowerSha256([string]$Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing required file: $Path"
    }
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-Plan($Manifest) {
    $result = [System.Collections.Generic.List[string]]::new()
    foreach ($stage in @($Manifest.compile_stages)) {
        foreach ($file in @($stage.files)) {
            $module = ([string]$file).Substring(0, ([string]$file).Length - 5).Replace('/', '.')
            $result.Add($module)
        }
    }
    return $result.ToArray()
}

function Get-OutputMap($Manifest) {
    $result = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $Manifest.outputs.PSObject.Properties) {
        $result.Add([string]$property.Name, ([string]$property.Value).ToLowerInvariant())
    }
    return $result
}

function Assert-PhysicalInputs($Manifest) {
    foreach ($property in $Manifest.inputs.PSObject.Properties) {
        $path = Join-Path $leanRoot (([string]$property.Name) -replace '/', '\')
        if ((Get-LowerSha256 $path) -ne ([string]$property.Value).ToLowerInvariant()) {
            throw "External input hash mismatch: $($property.Name)"
        }
    }
}

function Write-JsonAtomically($Value, [string]$Path, [int]$Depth) {
    $temporary = "$Path.tmp"
    $Value | ConvertTo-Json -Depth $Depth |
        Set-Content -LiteralPath $temporary -Encoding UTF8
    Move-Item -LiteralPath $temporary -Destination $Path -Force
}

$lockStream = $null
try {
    $lockStream = [System.IO.File]::Open(
        $lockPath,
        [System.IO.FileMode]::OpenOrCreate,
        [System.IO.FileAccess]::ReadWrite,
        [System.IO.FileShare]::None
    )

    $active = @(Get-CimInstance Win32_Process | Where-Object {
        $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe') -or
        ($_.CommandLine -match 'run_z180_k30_d6_algebraic_v97' -and
            $_.ProcessId -ne $PID)
    })
    if ($active.Count -ne 0) {
        throw 'Serial Lean window is not free for the post-UBridge migration.'
    }

    if ((Get-LowerSha256 $generatorPath) -ne $expectedGeneratorSha) {
        throw 'D6 generator hash differs from the post-UBridge policy.'
    }
    if ((Get-LowerSha256 $oldManifestPath) -ne $expectedOldManifestSha) {
        throw 'Authenticated prior D6 manifest backup is unavailable or drifted.'
    }
    if ((Get-LowerSha256 $manifestPath) -ne $expectedNewManifestSha) {
        throw 'Physical D6 manifest differs from the post-UBridge policy.'
    }

    $oldManifest = Get-Content -Raw -LiteralPath $oldManifestPath | ConvertFrom-Json
    $newManifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
    if (([string]$newManifest.generator_sha256).ToLowerInvariant() -ne $expectedGeneratorSha) {
        throw 'New D6 manifest does not pin the expected generator.'
    }
    $oldPlan = @(Get-Plan $oldManifest)
    $newPlan = @(Get-Plan $newManifest)
    if ($oldPlan.Count -ne 585 -or $newPlan.Count -ne 585) {
        throw 'D6 compile plan is not exactly 585 modules.'
    }
    for ($index = 0; $index -lt 585; $index += 1) {
        if ($oldPlan[$index] -ne $newPlan[$index]) {
            throw "D6 compile order changed at ordinal $index."
        }
    }
    if ($newPlan[583] -ne $uBridgeModule) {
        throw 'D6 UBridge is not compile ordinal 583.'
    }

    $oldOutputs = Get-OutputMap $oldManifest
    $newOutputs = Get-OutputMap $newManifest
    $changed = @(
        foreach ($key in $newOutputs.Keys) {
            if (-not $oldOutputs.ContainsKey($key) -or
                $oldOutputs[$key] -ne $newOutputs[$key]) {
                $key
            }
        }
    )
    if ($changed.Count -ne 1 -or $changed[0] -ne $uBridgeKey -or
        $newOutputs[$uBridgeKey] -ne $expectedBridgeSha) {
        throw 'The post-UBridge manifest delta is not exactly the corrected UBridge source.'
    }
    Assert-PhysicalInputs $newManifest
    foreach ($key in $newOutputs.Keys) {
        $source = Join-Path $leanRoot ($key -replace '/', '\')
        if ((Get-LowerSha256 $source) -ne $newOutputs[$key]) {
            throw "Generated D6 source does not match the new manifest: $key"
        }
    }

    $checkOutput = @(& python $generatorPath --check 2>&1)
    if ($LASTEXITCODE -ne 0) {
        throw "D6 generator check failed: $($checkOutput -join [Environment]::NewLine)"
    }

    $stateSha = Get-LowerSha256 $statePath
    $state = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
    if ($stateSha -eq $expectedNewManifestSha) {
        throw 'Unexpected state-file SHA collision with the manifest SHA.'
    }
    if ([string]$state.manifestSha256 -eq $expectedNewManifestSha -and
        @($state.completedModules).Count -eq 584 -and
        @($state.completedModules) -contains $uBridgeModule) {
        [ordered]@{ status = 'already-passed'; completedModuleCount = 584 } |
            ConvertTo-Json
        exit 0
    }
    if ($stateSha -ne $expectedOldStateSha -or
        ([string]$state.manifestSha256).ToLowerInvariant() -ne $expectedOldManifestSha) {
        throw 'D6 state is not the exact authenticated 583-module pre-migration state.'
    }

    $completed = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($module in @($state.completedModules)) {
        if (-not $completed.Add([string]$module)) {
            throw "Duplicate completed D6 module in state: $module"
        }
    }
    if ($completed.Count -ne 583) {
        throw "Expected exactly 583 completed D6 modules, found $($completed.Count)."
    }
    for ($index = 0; $index -lt 583; $index += 1) {
        $module = $newPlan[$index]
        if (-not $completed.Contains($module)) {
            throw "Completed D6 set is missing plan ordinal $index`: $module"
        }
        $key = ($module -replace '\.', '/') + '.lean'
        if ($oldOutputs[$key] -ne $newOutputs[$key]) {
            throw "A completed D6 source changed across the post-UBridge manifest: $key"
        }
        $olean = Join-Path $leanRoot (
            '.lake\build\lib\lean\' + ($module -replace '\.', '\') + '.olean'
        )
        if (-not (Test-Path -LiteralPath $olean -PathType Leaf)) {
            throw "Missing completed D6 olean: $module"
        }
    }

    $bridgeSource = Join-Path $leanRoot ($uBridgeKey -replace '/', '\')
    $bridgeOlean = Join-Path $leanRoot (
        '.lake\build\lib\lean\' + ($uBridgeModule -replace '\.', '\') + '.olean'
    )
    if ((Get-LowerSha256 $bridgeSource) -ne $expectedBridgeSha -or
        -not (Test-Path -LiteralPath $bridgeOlean -PathType Leaf) -or
        (Get-Item -LiteralPath $bridgeOlean).LastWriteTimeUtc -lt
            (Get-Item -LiteralPath $bridgeSource).LastWriteTimeUtc) {
        throw 'Corrected UBridge source/olean seal is missing or stale.'
    }

    $telemetryRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_v89_batch'
    $buildTelemetryPath = Join-Path $telemetryRoot "$uBridgeModule.build.json"
    $checkerTelemetryPath = Join-Path $telemetryRoot "$uBridgeModule.checker.json"
    $buildTelemetry = Get-Content -Raw -LiteralPath $buildTelemetryPath | ConvertFrom-Json
    $checkerTelemetry = Get-Content -Raw -LiteralPath $checkerTelemetryPath | ConvertFrom-Json
    foreach ($telemetry in @($buildTelemetry, $checkerTelemetry)) {
        if ([string]$telemetry.module -ne $uBridgeModule -or
            [string]$telemetry.status -ne 'passed' -or
            [int]$telemetry.exitCode -ne 0) {
            throw 'Corrected UBridge build/checker telemetry is not sealed PASS.'
        }
    }
    $buildLog = Get-Content -Raw -LiteralPath ([string]$buildTelemetry.stdoutPath)
    if ($buildLog -match 'sorryAx') {
        throw 'Corrected UBridge build reports sorryAx.'
    }

    $backupPath = Join-Path $auditRoot (
        'state-before-post-ubridge-fix-' + [Guid]::NewGuid().ToString('N') + '.json'
    )
    Copy-Item -LiteralPath $statePath -Destination $backupPath
    if ((Get-LowerSha256 $backupPath) -ne $expectedOldStateSha) {
        throw 'Post-UBridge state backup hash mismatch.'
    }

    $state.manifestSha256 = $expectedNewManifestSha
    $state.updatedAtUtc = [DateTime]::UtcNow.ToString('o')
    $state.completedModules = @($state.completedModules) + @($uBridgeModule)
    $state.records = @($state.records) + @(
        [ordered]@{
            module = $uBridgeModule
            phase = 'build'
            status = 'passed-before-state-migration'
            peakBytes = [uint64]$buildTelemetry.maxLeanWorkingSetBytes
            completedAtUtc = [string]$buildTelemetry.completedAtUtc
        },
        [ordered]@{
            module = $uBridgeModule
            phase = 'checker'
            status = 'passed-before-state-migration'
            peakBytes = [uint64]$checkerTelemetry.maxLeanWorkingSetBytes
            completedAtUtc = [string]$checkerTelemetry.completedAtUtc
        }
    )

    $candidate = "$statePath.tmp"
    $state | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath $candidate -Encoding UTF8
    $candidateState = Get-Content -Raw -LiteralPath $candidate | ConvertFrom-Json
    if (([string]$candidateState.manifestSha256).ToLowerInvariant() -ne
        $expectedNewManifestSha -or
        @($candidateState.completedModules).Count -ne 584 -or
        @($candidateState.completedModules) -notcontains $uBridgeModule) {
        throw 'Post-UBridge candidate state failed its final invariant check.'
    }
    Move-Item -LiteralPath $candidate -Destination $statePath -Force

    $migration = [ordered]@{
        schema = 'z180-k30-d6-algebraic-v97-post-ubridge-fix-migration-v1'
        migratedAtUtc = [DateTime]::UtcNow.ToString('o')
        oldManifestSha256 = $expectedOldManifestSha
        newManifestSha256 = $expectedNewManifestSha
        oldStateSha256 = $expectedOldStateSha
        newStateSha256 = Get-LowerSha256 $statePath
        completedModuleCount = 584
        preservedCompletedModuleCount = 583
        presealedModule = $uBridgeModule
        presealedBuildPeakBytes = [uint64]$buildTelemetry.maxLeanWorkingSetBytes
        presealedCheckerPeakBytes = [uint64]$checkerTelemetry.maxLeanWorkingSetBytes
        changedOutput = $uBridgeKey
        backupPath = $backupPath
        generatorCheckOutput = @($checkOutput)
    }
    Write-JsonAtomically $migration $migrationPath 6
    [ordered]@{ status = 'passed'; migration = $migration } | ConvertTo-Json -Depth 7
} finally {
    if ($null -ne $lockStream) {
        $lockStream.Dispose()
    }
}
