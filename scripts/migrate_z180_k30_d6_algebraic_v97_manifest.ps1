[CmdletBinding()]
param(
    [string]$ExpectedOldManifestSha =
        '89ffe0f277b2ba75927154209086ba1dd2c8d58bd26ce56f850e256e94cb1fc8',
    [int]$ExpectedCompletedModules = 573
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$generatorPath = Join-Path $leanRoot `
    'scripts\generate_z180_k30_d6_algebraic_v97.py'
$manifestPath = Join-Path $leanRoot `
    'generated\z180_k30_d6_algebraic_v97.manifest.json'
$auditRoot = Join-Path $workspaceRoot `
    'audit\z180_k30_projective_d6_algebraic_v97'
$statePath = Join-Path $auditRoot 'state.json'
$migrationPath = Join-Path $auditRoot 'manifest-migration.json'
$recoveryPath = Join-Path $auditRoot 'manifest-migration-recovery.json'
$lockPath = Join-Path $auditRoot 'manifest-migration.lock'
$policyOldManifestSha =
    '89ffe0f277b2ba75927154209086ba1dd2c8d58bd26ce56f850e256e94cb1fc8'
$policyGeneratorSha =
    '442f111a07fe80cc11783b19651569cfa4f1be59c55fd38c9e8007ad9b79cda9'
$policyNewManifestSha =
    '57897ef2aea94300564858463113fa7eb0938fde314cbdbdef51c6eb66b6ded1'
$policyCompletedModules = 573

if ($ExpectedOldManifestSha.ToLowerInvariant() -ne $policyOldManifestSha -or
    $ExpectedCompletedModules -ne $policyCompletedModules) {
    throw 'D6 migration policy parameters are immutable.'
}

function Get-LowerSha256 {
    param([string]$Path)
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-OutputHashMap {
    param([object]$Manifest)
    $result = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $Manifest.outputs.PSObject.Properties) {
        $result.Add(
            [string]$property.Name,
            ([string]$property.Value).ToLowerInvariant()
        )
    }
    return $result
}

function Get-InputHashMap {
    param([object]$Manifest)
    $result = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $Manifest.inputs.PSObject.Properties) {
        $result.Add(
            [string]$property.Name,
            ([string]$property.Value).ToLowerInvariant()
        )
    }
    return $result
}

function Assert-PhysicalInputs {
    param(
        [System.Collections.Generic.Dictionary[string, string]]$Inputs,
        [string]$Label
    )
    foreach ($key in $Inputs.Keys) {
        $inputPath = Join-Path $leanRoot ($key -replace '/', '\')
        if (-not (Test-Path -LiteralPath $inputPath -PathType Leaf) -or
            (Get-LowerSha256 $inputPath) -ne $Inputs[$key]) {
            throw "$Label physical input hash mismatch: $key"
        }
    }
}

function Convert-FileToModule {
    param([string]$File)
    return (($File -replace '\.lean$', '') -replace '/', '.')
}

function Convert-ModuleToOutputKey {
    param([string]$Module)
    return (($Module -replace '\.', '/') + '.lean')
}

function Get-CompilePlan {
    param([object]$Manifest)
    $result = @(
        foreach ($stage in @($Manifest.compile_stages)) {
            foreach ($file in @($stage.files)) {
                Convert-FileToModule ([string]$file)
            }
        }
    )
    return $result
}

function Assert-Topology {
    param([object]$Manifest, [string]$Label)
    $expectedKinds = @(
        'core',
        'nat_index_leaves',
        'nat_index_aggregate',
        'rawset_comb_leaves',
        'bounded_bridge_rows',
        'u_bridge_aggregate',
        'v_singleton'
    )
    $expectedCounts = @(1, 256, 1, 315, 10, 1, 1)
    $stages = @($Manifest.compile_stages)
    if ($stages.Count -ne $expectedKinds.Count) {
        throw "$Label manifest has $($stages.Count) stages, expected 7."
    }
    for ($index = 0; $index -lt $expectedKinds.Count; $index += 1) {
        if ([string]$stages[$index].kind -ne $expectedKinds[$index]) {
            throw "$Label stage $index kind drifted."
        }
        if (@($stages[$index].files).Count -ne $expectedCounts[$index]) {
            throw "$Label stage $index file count drifted."
        }
    }
    $plan = @(Get-CompilePlan $Manifest)
    $unique = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($module in $plan) {
        if (-not $unique.Add([string]$module)) {
            throw "$Label compile plan contains duplicate module $module."
        }
    }
    if ($plan.Count -ne 585 -or $unique.Count -ne 585) {
        throw "$Label compile plan is not an exact 585-module sequence."
    }
    $expectedLastLeaf =
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicLeaf314PilotV97'
    $expectedFirstBridge =
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow00PilotV97'
    if ($plan[572] -ne $expectedLastLeaf -or
        $plan[573] -ne $expectedFirstBridge) {
        throw "$Label pre-Bridge ordinal boundary drifted."
    }
}

function Assert-ExactCompletedPrefix {
    param(
        [object[]]$CompletedModules,
        [string[]]$Plan,
        [int]$PrefixLength,
        [string]$Label
    )
    if ($CompletedModules.Count -ne $PrefixLength) {
        throw "$Label completed count is $($CompletedModules.Count), expected $PrefixLength."
    }
    $completedSet = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($moduleObject in $CompletedModules) {
        $module = [string]$moduleObject
        if (-not $completedSet.Add($module)) {
            throw "$Label completed state contains duplicate $module."
        }
    }
    for ($index = 0; $index -lt $PrefixLength; $index += 1) {
        if (-not $completedSet.Contains($Plan[$index])) {
            throw "$Label completed state is not the exact compile prefix at $index."
        }
    }
}

function Assert-PhysicalOutputs {
    param(
        [System.Collections.Generic.Dictionary[string, string]]$Outputs,
        [string]$Label
    )
    foreach ($key in $Outputs.Keys) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf) -or
            (Get-LowerSha256 $sourcePath) -ne $Outputs[$key]) {
            throw "$Label physical source hash mismatch: $key"
        }
    }
}

function Assert-CompletedOleANs {
    param([object[]]$CompletedModules, [string]$Label)
    foreach ($moduleObject in $CompletedModules) {
        $module = [string]$moduleObject
        $oleanPath = Join-Path $leanRoot (
            '.lake\build\lib\lean\' + ($module -replace '\.', '\') + '.olean'
        )
        if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            throw "$Label missing completed olean: $module"
        }
    }
}

function Write-JsonAtomically {
    param([object]$Value, [string]$Path, [int]$Depth)
    $temporary = "$Path.tmp"
    $Value | ConvertTo-Json -Depth $Depth |
        Set-Content -LiteralPath $temporary -Encoding UTF8
    Move-Item -LiteralPath $temporary -Destination $Path -Force
}

function Restore-OldSnapshot {
    param(
        [string]$BackupRoot,
        [System.Collections.Generic.Dictionary[string, string]]$OldOutputs,
        [System.Collections.Generic.Dictionary[string, string]]$ExpectedNewOutputs,
        [System.Collections.Generic.Dictionary[string, string]]$SnapshotOutputs,
        [string]$ExpectedOldManifestSha,
        [string]$ExpectedNewManifestSha,
        [string]$OldStateSha,
        [string]$ExpectedNewStateSha
    )
    $restoreKeys = [System.Collections.Generic.List[string]]::new()
    $backupManifestPath = Join-Path $BackupRoot 'old-manifest.json'
    $backupStatePath = Join-Path $BackupRoot 'old-state.json'
    if (-not (Test-Path -LiteralPath $backupManifestPath -PathType Leaf) -or
        -not (Test-Path -LiteralPath $backupStatePath -PathType Leaf) -or
        (Get-LowerSha256 $backupManifestPath) -ne $ExpectedOldManifestSha -or
        (Get-LowerSha256 $backupStatePath) -ne $OldStateSha) {
        throw 'Rollback backup manifest/state preflight failed.'
    }
    $backupManifest = Get-Content -Raw -LiteralPath $backupManifestPath |
        ConvertFrom-Json
    $backupManifestOutputs = Get-OutputHashMap $backupManifest
    if ($backupManifestOutputs.Count -ne $OldOutputs.Count) {
        throw 'Rollback backup output census drifted.'
    }
    foreach ($key in $OldOutputs.Keys) {
        if (-not $backupManifestOutputs.ContainsKey($key) -or
            $backupManifestOutputs[$key] -ne $OldOutputs[$key]) {
            throw "Rollback backup manifest output map drifted: $key"
        }
    }
    if ($SnapshotOutputs.Count -ne $OldOutputs.Count) {
        throw 'Rollback snapshot output census drifted.'
    }
    foreach ($key in $SnapshotOutputs.Keys) {
        $backupSource = Join-Path $BackupRoot (
            'sources\' + ($key -replace '/', '\')
        )
        if (-not (Test-Path -LiteralPath $backupSource -PathType Leaf) -or
            (Get-LowerSha256 $backupSource) -ne $SnapshotOutputs[$key]) {
            throw "Rollback snapshot backup preflight failed: $key"
        }
    }
    foreach ($key in $OldOutputs.Keys) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
            throw "Rollback refuses to overwrite missing/external source: $key"
        }
        $currentSha = Get-LowerSha256 $sourcePath
        if ($currentSha -eq $OldOutputs[$key]) {
            continue
        }
        if ($ExpectedNewOutputs.ContainsKey($key) -and
            $currentSha -eq $ExpectedNewOutputs[$key]) {
            $backupSource = Join-Path $BackupRoot (
                'sources\' + ($key -replace '/', '\')
            )
            if (-not $SnapshotOutputs.ContainsKey($key)) {
                throw "Rollback backup source preflight failed: $key"
            }
            [void]$restoreKeys.Add($key)
            continue
        }
        throw "Rollback refuses to overwrite third-party source drift: $key"
    }
    $currentManifestSha = Get-LowerSha256 $manifestPath
    $oldManifestSha = Get-LowerSha256 $backupManifestPath
    if ($currentManifestSha -ne $oldManifestSha -and
        $currentManifestSha -ne $ExpectedNewManifestSha) {
        throw 'Rollback refuses to overwrite third-party manifest drift.'
    }
    $currentStateSha = Get-LowerSha256 $statePath
    if ($currentStateSha -ne $OldStateSha -and
        ($ExpectedNewStateSha -eq '' -or
            $currentStateSha -ne $ExpectedNewStateSha)) {
        throw 'Rollback refuses to overwrite externally changed D6 state.'
    }
    # All compare-and-swap preconditions passed; only now mutate rollback targets.
    foreach ($key in $restoreKeys) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        $backupSource = Join-Path $BackupRoot (
            'sources\' + ($key -replace '/', '\')
        )
        Copy-Item -LiteralPath $backupSource -Destination $sourcePath -Force
    }
    if ($currentManifestSha -eq $ExpectedNewManifestSha) {
        Copy-Item -LiteralPath (Join-Path $BackupRoot 'old-manifest.json') `
            -Destination $manifestPath -Force
    }
    if ($currentStateSha -eq $ExpectedNewStateSha -and
        $currentStateSha -ne $OldStateSha) {
        Copy-Item -LiteralPath (Join-Path $BackupRoot 'old-state.json') `
            -Destination $statePath -Force
    }
}

function Remove-TransactionMigrationMarker {
    param([string]$OldManifestSha, [string]$NewManifestSha)
    if (-not (Test-Path -LiteralPath $migrationPath -PathType Leaf)) {
        return
    }
    $marker = Get-Content -Raw -LiteralPath $migrationPath | ConvertFrom-Json
    if ([string]$marker.oldManifestSha256 -ne $OldManifestSha -or
        [string]$marker.newManifestSha256 -ne $NewManifestSha -or
        [string]$marker.schema -ne
            'z180-k30-d6-algebraic-v97-manifest-migration-v2') {
        throw 'Refusing to remove a foreign D6 migration marker.'
    }
    Remove-Item -LiteralPath $migrationPath -Force
}

New-Item -ItemType Directory -Path $auditRoot -Force | Out-Null
try {
    $lockStream = [System.IO.File]::Open(
        $lockPath,
        [System.IO.FileMode]::OpenOrCreate,
        [System.IO.FileAccess]::ReadWrite,
        [System.IO.FileShare]::None
    )
} catch [System.IO.IOException] {
    throw 'Another D6 manifest migration owns the exclusive lock.'
}

$committed = $false
$backupRoot = $null
$oldOutputs = $null
$plannedOutputs = $null
$oldStateSha = $null
$expectedNewStateSha = ''
$writeStarted = $false
try {
    $active = @(Get-CimInstance Win32_Process | Where-Object {
        $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe')
    })
    if ($active.Count -ne 0) {
        throw 'D6 manifest migration requires a clean serial Lean boundary.'
    }
    $activeDriver = @(Get-CimInstance Win32_Process | Where-Object {
        $_.Name -eq 'powershell.exe' -and
        $null -ne $_.CommandLine -and
        $_.CommandLine.Contains('run_z180_k30_d6_algebraic_v97.ps1')
    })
    if ($activeDriver.Count -ne 0) {
        throw 'D6 manifest migration requires the serial driver to have exited.'
    }
    if (-not (Test-Path -LiteralPath $statePath -PathType Leaf)) {
        throw 'Missing D6 serial state.'
    }
    if ((Get-LowerSha256 $generatorPath) -ne $policyGeneratorSha) {
        throw 'Physical D6 generator SHA differs from migration policy.'
    }

    # Recover a prior interrupted transaction before beginning a new one.
    if (Test-Path -LiteralPath $recoveryPath -PathType Leaf) {
        $recovery = Get-Content -Raw -LiteralPath $recoveryPath | ConvertFrom-Json
        $recoveryBackup = [string]$recovery.backupRoot
        $resolvedAudit = [IO.Path]::GetFullPath($auditRoot).TrimEnd('\') + '\'
        $resolvedBackup = [IO.Path]::GetFullPath($recoveryBackup)
        if (-not $resolvedBackup.StartsWith(
            $resolvedAudit,
            [StringComparison]::OrdinalIgnoreCase
        )) {
            throw 'Recovery backup escaped the D6 audit root.'
        }
        $backupManifest = Get-Content -Raw -LiteralPath (
            Join-Path $resolvedBackup 'old-manifest.json'
        ) | ConvertFrom-Json
        $backupOutputs = Get-OutputHashMap $backupManifest
        $snapshotOutputs = [System.Collections.Generic.Dictionary[string, string]]::new(
            [System.StringComparer]::Ordinal
        )
        foreach ($property in $recovery.snapshotOutputsSha256.PSObject.Properties) {
            $snapshotOutputs.Add(
                [string]$property.Name,
                ([string]$property.Value).ToLowerInvariant()
            )
        }
        $plannedManifestPath = Join-Path $resolvedBackup 'planned-manifest.json'
        $plannedManifest = Get-Content -Raw -LiteralPath $plannedManifestPath |
            ConvertFrom-Json
        $plannedOutputs = Get-OutputHashMap $plannedManifest
        $currentState = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
        $physicalManifestSha = Get-LowerSha256 $manifestPath
        $expectedNew = [string]$recovery.expectedNewManifestSha256
        $recoveryNewStateSha = [string]$recovery.expectedNewStateSha256
        if ($expectedNew -and
            [string]$currentState.manifestSha256 -eq $expectedNew -and
            $physicalManifestSha -eq $expectedNew -and
            $recoveryNewStateSha -ne '' -and
            (Get-LowerSha256 $statePath) -eq $recoveryNewStateSha) {
            if ($expectedNew -ne $policyNewManifestSha) {
                throw 'Committed recovery manifest SHA differs from policy.'
            }
            if (([string]$plannedManifest.generator_sha256).ToLowerInvariant() -ne
                $policyGeneratorSha) {
                throw 'Committed recovery generator pin differs from policy.'
            }
            Assert-Topology $plannedManifest 'committed recovery'
            $recoveryPlan = @(Get-CompilePlan $plannedManifest)
            $recoveryCompleted = @($currentState.completedModules)
            Assert-ExactCompletedPrefix `
                $recoveryCompleted $recoveryPlan $ExpectedCompletedModules `
                'committed recovery'
            Assert-PhysicalOutputs $plannedOutputs 'committed recovery'
            $recoveryInputs = Get-InputHashMap $plannedManifest
            Assert-PhysicalInputs $recoveryInputs 'committed recovery'
            Assert-CompletedOleANs $recoveryCompleted 'committed recovery'
            Remove-Item -LiteralPath $recoveryPath -Force
            $committed = $true
            [ordered]@{
                status = 'already-committed'
                newManifestSha256 = $expectedNew
                completedModuleCount = $recoveryCompleted.Count
                backupRoot = $resolvedBackup
            } | ConvertTo-Json -Depth 4
            return
        } else {
            Restore-OldSnapshot `
                $resolvedBackup $backupOutputs $plannedOutputs $snapshotOutputs `
                ([string]$recovery.oldManifestSha256) $expectedNew `
                ([string]$recovery.oldStateSha256) `
                $recoveryNewStateSha
            Remove-TransactionMigrationMarker `
                ([string]$recovery.oldManifestSha256) $expectedNew
            Remove-Item -LiteralPath $recoveryPath -Force
        }
    }

    $state = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
    $oldManifestSha = Get-LowerSha256 $manifestPath
    if ($oldManifestSha -ne $ExpectedOldManifestSha.ToLowerInvariant()) {
        throw "Unexpected old D6 manifest SHA: $oldManifestSha"
    }
    if ([string]$state.manifestSha256 -ne $oldManifestSha) {
        throw 'D6 state is not pinned to the physical old manifest.'
    }

    $oldManifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
    Assert-Topology $oldManifest 'old'
    $oldPlan = @(Get-CompilePlan $oldManifest)
    $completedModules = @($state.completedModules)
    Assert-ExactCompletedPrefix `
        $completedModules $oldPlan $ExpectedCompletedModules 'old'
    $oldOutputs = Get-OutputHashMap $oldManifest
    $oldInputs = Get-InputHashMap $oldManifest
    Assert-PhysicalInputs $oldInputs 'old'
    $oldStateSha = Get-LowerSha256 $statePath

    $completedKeys = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($moduleObject in $completedModules) {
        $module = [string]$moduleObject
        $key = Convert-ModuleToOutputKey $module
        if (-not $oldOutputs.ContainsKey($key)) {
            throw "Completed module is absent from old manifest: $module"
        }
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        if ((Get-LowerSha256 $sourcePath) -ne $oldOutputs[$key]) {
            throw "Completed source drifted before migration: $key"
        }
        $oleanPath = Join-Path $leanRoot (
            '.lake\build\lib\lean\' + ($module -replace '\.', '\') + '.olean'
        )
        if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            throw "Missing completed olean before migration: $module"
        }
        [void]$completedKeys.Add($key)
    }

    $backupRoot = Join-Path $auditRoot (
        'manifest-migration-backup-' + [Guid]::NewGuid().ToString('N')
    )
    New-Item -ItemType Directory -Path $backupRoot -Force | Out-Null
    Copy-Item -LiteralPath $manifestPath `
        -Destination (Join-Path $backupRoot 'old-manifest.json')
    Copy-Item -LiteralPath $statePath `
        -Destination (Join-Path $backupRoot 'old-state.json')
    foreach ($key in $oldOutputs.Keys) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        $backupSource = Join-Path $backupRoot (
            'sources\' + ($key -replace '/', '\')
        )
        New-Item -ItemType Directory -Path (Split-Path -Parent $backupSource) `
            -Force | Out-Null
        Copy-Item -LiteralPath $sourcePath -Destination $backupSource
    }
    $snapshotOutputs = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($key in ($oldOutputs.Keys | Sort-Object)) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        $snapshotOutputs.Add($key, (Get-LowerSha256 $sourcePath))
    }

    $plannedManifestPath = Join-Path $backupRoot 'planned-manifest.json'
    $planCode = @'
import importlib.util
import pathlib
import sys

generator_path = pathlib.Path(sys.argv[1]).resolve()
output_path = pathlib.Path(sys.argv[2]).resolve()
spec = importlib.util.spec_from_file_location('z180_d6_plan', generator_path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
_, manifest = module.build()
with output_path.open('w', encoding='utf-8', newline='\n') as stream:
    stream.write(module.manifest_text(manifest))
'@
    $planOutput = @(
        & python -c $planCode $generatorPath $plannedManifestPath 2>&1
    )
    if ($LASTEXITCODE -ne 0) {
        throw "D6 in-memory manifest plan failed: $($planOutput -join [Environment]::NewLine)"
    }
    $plannedManifestSha = Get-LowerSha256 $plannedManifestPath
    if ($plannedManifestSha -ne $policyNewManifestSha) {
        throw "Planned D6 manifest SHA differs from policy: $plannedManifestSha"
    }
    $plannedManifest = Get-Content -Raw -LiteralPath $plannedManifestPath |
        ConvertFrom-Json
    if (([string]$plannedManifest.generator_sha256).ToLowerInvariant() -ne
        $policyGeneratorSha) {
        throw 'Planned manifest generator pin differs from policy.'
    }
    Assert-Topology $plannedManifest 'planned'
    $plannedPlan = @(Get-CompilePlan $plannedManifest)
    for ($index = 0; $index -lt $oldPlan.Count; $index += 1) {
        if ($plannedPlan[$index] -ne $oldPlan[$index]) {
            throw "Planned compile order drifted at ordinal $index."
        }
    }
    Assert-ExactCompletedPrefix `
        $completedModules $plannedPlan $ExpectedCompletedModules 'planned'
    $plannedOutputs = Get-OutputHashMap $plannedManifest
    $plannedInputs = Get-InputHashMap $plannedManifest
    if ($plannedInputs.Count -ne $oldInputs.Count) {
        throw 'Planned external input count drifted.'
    }
    foreach ($key in $oldInputs.Keys) {
        if (-not $plannedInputs.ContainsKey($key) -or
            $plannedInputs[$key] -ne $oldInputs[$key]) {
            throw "Planned external input hash drifted: $key"
        }
    }
    Assert-PhysicalInputs $plannedInputs 'planned'
    $plannedChangedOutputs = @(
        foreach ($key in $plannedOutputs.Keys) {
            if (-not $oldOutputs.ContainsKey($key) -or
                $oldOutputs[$key] -ne $plannedOutputs[$key]) {
                $key
            }
        }
    ) | Sort-Object
    $expectedChanged = @(
        0..9 | ForEach-Object {
            'Fuglede/Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow' +
            ('{0:D2}' -f $_) + 'PilotV97.lean'
        }
        'Fuglede/Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97.lean'
        'Fuglede/Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97.lean'
    ) | Sort-Object
    if ($plannedChangedOutputs.Count -ne $expectedChanged.Count) {
        throw 'Planned changed-output count differs from policy.'
    }
    for ($index = 0; $index -lt $expectedChanged.Count; $index += 1) {
        if ($plannedChangedOutputs[$index] -ne $expectedChanged[$index]) {
            throw "Unexpected planned changed output: $($plannedChangedOutputs[$index])"
        }
    }
    foreach ($key in $oldOutputs.Keys) {
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        $currentSha = Get-LowerSha256 $sourcePath
        if ($currentSha -ne $oldOutputs[$key] -and
            (-not $plannedOutputs.ContainsKey($key) -or
                $currentSha -ne $plannedOutputs[$key])) {
            throw "Pre-write source has third-party drift: $key"
        }
    }
    $recovery = [ordered]@{
        schema = 'z180-k30-d6-algebraic-v97-migration-recovery-v1'
        backupRoot = $backupRoot
        oldManifestSha256 = $oldManifestSha
        oldStateSha256 = $oldStateSha
        expectedNewManifestSha256 = $policyNewManifestSha
        expectedNewStateSha256 = ''
        snapshotOutputsSha256 = $snapshotOutputs
        preparedAtUtc = [DateTime]::UtcNow.ToString('o')
    }
    Write-JsonAtomically $recovery $recoveryPath 5

    $writeStarted = $true
    $writeOutput = @(& python $generatorPath --write 2>&1)
    if ($LASTEXITCODE -ne 0) {
        throw "D6 generator --write failed: $($writeOutput -join [Environment]::NewLine)"
    }
    $checkOutput = @(& python $generatorPath --check 2>&1)
    if ($LASTEXITCODE -ne 0) {
        throw "D6 generator --check failed: $($checkOutput -join [Environment]::NewLine)"
    }

    $newManifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
    $newManifestSha = Get-LowerSha256 $manifestPath
    if ($newManifestSha -ne $policyNewManifestSha) {
        throw "Refreshed D6 manifest SHA differs from policy: $newManifestSha"
    }
    if (([string]$newManifest.generator_sha256).ToLowerInvariant() -ne
        $policyGeneratorSha) {
        throw 'Refreshed manifest generator pin differs from policy.'
    }
    Assert-Topology $newManifest 'refreshed'
    $newPlan = @(Get-CompilePlan $newManifest)
    for ($index = 0; $index -lt $oldPlan.Count; $index += 1) {
        if ($newPlan[$index] -ne $oldPlan[$index]) {
            throw "Refreshed compile order drifted at ordinal $index."
        }
    }
    Assert-ExactCompletedPrefix `
        $completedModules $newPlan $ExpectedCompletedModules 'refreshed'
    $newOutputs = Get-OutputHashMap $newManifest
    $newInputs = Get-InputHashMap $newManifest
    if ($newInputs.Count -ne $oldInputs.Count) {
        throw 'Refreshed external input count drifted.'
    }
    foreach ($key in $oldInputs.Keys) {
        if (-not $newInputs.ContainsKey($key) -or
            $newInputs[$key] -ne $oldInputs[$key]) {
            throw "Refreshed external input hash drifted: $key"
        }
    }
    Assert-PhysicalInputs $newInputs 'refreshed'
    if ($newOutputs.Count -ne 585) {
        throw "Unexpected refreshed D6 output count: $($newOutputs.Count)"
    }
    Assert-PhysicalOutputs $newOutputs 'refreshed'

    foreach ($key in $completedKeys) {
        if (-not $newOutputs.ContainsKey($key) -or
            $oldOutputs[$key] -ne $newOutputs[$key]) {
            throw "Completed output hash changed across refresh: $key"
        }
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        if ((Get-LowerSha256 $sourcePath) -ne $newOutputs[$key]) {
            throw "Completed physical source mismatches refreshed manifest: $key"
        }
    }

    $changedOutputs = @(
        foreach ($key in $newOutputs.Keys) {
            if (-not $oldOutputs.ContainsKey($key) -or
                $oldOutputs[$key] -ne $newOutputs[$key]) {
                if ($completedKeys.Contains($key)) {
                    throw "Refresh changed a completed module: $key"
                }
                $key
            }
        }
    ) | Sort-Object
    $expectedChanged = @(
        0..9 | ForEach-Object {
            'Fuglede/Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow' +
            ('{0:D2}' -f $_) + 'PilotV97.lean'
        }
        'Fuglede/Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97.lean'
        'Fuglede/Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97.lean'
    ) | Sort-Object
    if ($changedOutputs.Count -ne $expectedChanged.Count) {
        throw "Unexpected number of changed uncompleted outputs: $($changedOutputs.Count)"
    }
    for ($index = 0; $index -lt $expectedChanged.Count; $index += 1) {
        if ($changedOutputs[$index] -ne $expectedChanged[$index]) {
            throw "Unexpected changed uncompleted output: $($changedOutputs[$index])"
        }
    }

    $migration = [ordered]@{
        schema = 'z180-k30-d6-algebraic-v97-manifest-migration-v2'
        migratedAtUtc = [DateTime]::UtcNow.ToString('o')
        oldManifestSha256 = $oldManifestSha
        newManifestSha256 = $newManifestSha
        completedModuleCount = $completedModules.Count
        completedPrefixExact = $true
        compileTopologyPreserved = $true
        completedHashesPreserved = $true
        completedOleANsPresent = $true
        changedUncompletedOutputs = $changedOutputs
        backupRoot = $backupRoot
        generatorWriteOutput = @($writeOutput)
        generatorCheckOutput = @($checkOutput)
    }
    $state.manifestSha256 = $newManifestSha
    $state.updatedAtUtc = [DateTime]::UtcNow.ToString('o')
    if ($null -eq $state.PSObject.Properties['manifestMigrations']) {
        $state | Add-Member -NotePropertyName manifestMigrations -NotePropertyValue @()
    }
    $state.manifestMigrations = @($state.manifestMigrations) + @($migration)

    # Prepare and authenticate the exact state bytes before the atomic commit move.
    $stateTemporary = "$statePath.tmp"
    $state | ConvertTo-Json -Depth 12 |
        Set-Content -LiteralPath $stateTemporary -Encoding UTF8
    $expectedNewStateSha = Get-LowerSha256 $stateTemporary
    $recovery.expectedNewManifestSha256 = $newManifestSha
    $recovery.expectedNewStateSha256 = $expectedNewStateSha
    Write-JsonAtomically $recovery $recoveryPath 5

    # Commit marker first; the state pin moves last and defines transaction commit.
    Write-JsonAtomically $migration $migrationPath 8
    Move-Item -LiteralPath $stateTemporary -Destination $statePath -Force
    $committed = $true
    Remove-Item -LiteralPath $recoveryPath -Force

    [ordered]@{
        status = 'passed'
        oldManifestSha256 = $oldManifestSha
        newManifestSha256 = $newManifestSha
        completedModuleCount = $completedModules.Count
        changedUncompletedOutputCount = $changedOutputs.Count
        changedUncompletedOutputs = $changedOutputs
        backupRoot = $backupRoot
    } | ConvertTo-Json -Depth 5
} catch {
    if (-not $committed -and $writeStarted -and
        $null -ne $backupRoot -and $null -ne $oldOutputs -and
        $null -ne $plannedOutputs -and $null -ne $oldStateSha) {
        Restore-OldSnapshot `
            $backupRoot $oldOutputs $plannedOutputs $snapshotOutputs `
            $policyOldManifestSha $policyNewManifestSha `
            $oldStateSha $expectedNewStateSha
        Remove-TransactionMigrationMarker `
            $ExpectedOldManifestSha.ToLowerInvariant() $policyNewManifestSha
        if (Test-Path -LiteralPath $recoveryPath -PathType Leaf) {
            Remove-Item -LiteralPath $recoveryPath -Force
        }
    }
    throw
} finally {
    if ($null -ne $lockStream) {
        $lockStream.Dispose()
    }
}
