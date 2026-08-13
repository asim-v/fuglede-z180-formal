param()

$ErrorActionPreference = 'Stop'
$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_d6_algebraic_v97'
$statePath = Join-Path $auditRoot 'state.json'
$manifestPath = Join-Path $leanRoot 'generated\z180_k30_d6_algebraic_v97.manifest.json'
$generatorPath = Join-Path $leanRoot 'scripts\generate_z180_k30_d6_algebraic_v97.py'
$oldManifestPath = Join-Path $auditRoot 'reconstructed-manifest-before-d6v-fix-7c16fb75.json'
$migrationPath = Join-Path $auditRoot 'post-d6v-fix-migration.json'
$lockPath = Join-Path $auditRoot 'post-d6v-fix-migration.lock'

$oldStateSha = 'd6e9d882d34fee9c2f23ee6867b7e0ac44fc65abd8df85cb90da9b050b953d8d'
$oldManifestSha = '7c16fb75e67cb75a73ad8e5444c9bb3d9ba4875d466d416f5921f2300ae22cee'
$newManifestSha = 'f3e25a8480f420686baf8c7e43a4f020a05e684eaa824a268f19d3e4b50e2433'
$generatorSha = 'c586175e2ee3ef887480343ea09c20047f506ec6c0e172740427d067dc7b49c2'
$d6vModule = 'Fuglede.Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97'
$d6vKey = 'Fuglede/Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97.lean'
$d6vSha = '549d6f3d9bd835e000b62ed9ad74142a90af23211ad45de47fecf77c97abf24c'

function Get-Sha([string]$Path) {
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing required file: $Path"
    }
    (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-Plan($Manifest) {
    $result = [System.Collections.Generic.List[string]]::new()
    foreach ($stage in @($Manifest.compile_stages)) {
        foreach ($file in @($stage.files)) {
            $result.Add((([string]$file).Substring(0, ([string]$file).Length - 5)).Replace('/', '.'))
        }
    }
    $result.ToArray()
}

function Get-Outputs($Manifest) {
    $result = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $Manifest.outputs.PSObject.Properties) {
        $result.Add([string]$property.Name, ([string]$property.Value).ToLowerInvariant())
    }
    $result
}

function Write-JsonAtomic($Value, [string]$Path, [int]$Depth) {
    $temporary = "$Path.tmp"
    $Value | ConvertTo-Json -Depth $Depth | Set-Content -LiteralPath $temporary -Encoding UTF8
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
        throw 'Serial Lean window is not free for the D6V source migration.'
    }

    if ((Get-Sha $oldManifestPath) -ne $oldManifestSha -or
        (Get-Sha $manifestPath) -ne $newManifestSha -or
        (Get-Sha $generatorPath) -ne $generatorSha) {
        throw 'D6V migration source/manifest/generator pin mismatch.'
    }
    $oldManifest = Get-Content -Raw -LiteralPath $oldManifestPath | ConvertFrom-Json
    $newManifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
    if (([string]$newManifest.generator_sha256).ToLowerInvariant() -ne $generatorSha) {
        throw 'New D6 manifest does not pin the corrected D6V generator.'
    }
    $oldPlan = @(Get-Plan $oldManifest)
    $newPlan = @(Get-Plan $newManifest)
    if ($oldPlan.Count -ne 585 -or $newPlan.Count -ne 585) {
        throw 'D6 plan length changed during the D6V correction.'
    }
    for ($index = 0; $index -lt 585; $index += 1) {
        if ($oldPlan[$index] -ne $newPlan[$index]) {
            throw "D6 plan changed at ordinal $index."
        }
    }
    if ($newPlan[584] -ne $d6vModule) {
        throw 'D6V is not the final module in the authenticated plan.'
    }
    $oldOutputs = Get-Outputs $oldManifest
    $newOutputs = Get-Outputs $newManifest
    $changed = @(
        foreach ($key in $newOutputs.Keys) {
            if ($oldOutputs[$key] -ne $newOutputs[$key]) { $key }
        }
    )
    if ($changed.Count -ne 1 -or $changed[0] -ne $d6vKey -or
        $newOutputs[$d6vKey] -ne $d6vSha) {
        throw 'Manifest delta is not exactly the corrected final D6V module.'
    }

    foreach ($property in $newManifest.inputs.PSObject.Properties) {
        $path = Join-Path $leanRoot (([string]$property.Name) -replace '/', '\')
        if ((Get-Sha $path) -ne ([string]$property.Value).ToLowerInvariant()) {
            throw "D6 external input drift: $($property.Name)"
        }
    }
    foreach ($key in $newOutputs.Keys) {
        $path = Join-Path $leanRoot ($key -replace '/', '\')
        if ((Get-Sha $path) -ne $newOutputs[$key]) {
            throw "D6 generated output drift: $key"
        }
    }
    $checkOutput = @(& python $generatorPath --check 2>&1)
    if ($LASTEXITCODE -ne 0) {
        throw "D6 generator check failed: $($checkOutput -join [Environment]::NewLine)"
    }

    if ((Get-Sha $statePath) -ne $oldStateSha) {
        throw 'D6 state bytes differ from the authenticated 584-module state.'
    }
    $state = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
    if (([string]$state.manifestSha256).ToLowerInvariant() -ne $oldManifestSha) {
        throw 'D6 state is not pinned to the pre-D6V manifest.'
    }
    $completed = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($module in @($state.completedModules)) {
        if (-not $completed.Add([string]$module)) {
            throw "Duplicate completed D6 module: $module"
        }
    }
    if ($completed.Count -ne 584 -or $completed.Contains($d6vModule)) {
        throw 'D6 state is not exactly pre-D6V with 584 completed modules.'
    }
    for ($index = 0; $index -lt 584; $index += 1) {
        $module = $newPlan[$index]
        if (-not $completed.Contains($module)) {
            throw "D6 state misses completed plan ordinal $index`: $module"
        }
        $key = ($module -replace '\.', '/') + '.lean'
        if ($oldOutputs[$key] -ne $newOutputs[$key]) {
            throw "Completed D6 source changed during D6V correction: $key"
        }
        $olean = Join-Path $leanRoot (
            '.lake\build\lib\lean\' + ($module -replace '\.', '\') + '.olean'
        )
        if (-not (Test-Path -LiteralPath $olean -PathType Leaf)) {
            throw "Missing completed D6 olean: $module"
        }
    }

    $backup = Join-Path $auditRoot (
        'state-before-post-d6v-fix-' + [Guid]::NewGuid().ToString('N') + '.json'
    )
    Copy-Item -LiteralPath $statePath -Destination $backup
    if ((Get-Sha $backup) -ne $oldStateSha) {
        throw 'D6V migration state backup hash mismatch.'
    }
    $state.manifestSha256 = $newManifestSha
    $state.updatedAtUtc = [DateTime]::UtcNow.ToString('o')
    $candidate = "$statePath.tmp"
    $state | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath $candidate -Encoding UTF8
    $candidateState = Get-Content -Raw -LiteralPath $candidate | ConvertFrom-Json
    if (([string]$candidateState.manifestSha256).ToLowerInvariant() -ne
        $newManifestSha -or @($candidateState.completedModules).Count -ne 584) {
        throw 'D6V migration candidate state failed validation.'
    }
    Move-Item -LiteralPath $candidate -Destination $statePath -Force

    $migration = [ordered]@{
        schema = 'z180-k30-d6-algebraic-v97-post-d6v-fix-migration-v1'
        migratedAtUtc = [DateTime]::UtcNow.ToString('o')
        oldManifestSha256 = $oldManifestSha
        newManifestSha256 = $newManifestSha
        oldStateSha256 = $oldStateSha
        newStateSha256 = Get-Sha $statePath
        preservedCompletedModuleCount = 584
        changedOutput = $d6vKey
        backupPath = $backup
        generatorCheckOutput = @($checkOutput)
    }
    Write-JsonAtomic $migration $migrationPath 5
    [ordered]@{ status = 'passed'; migration = $migration } | ConvertTo-Json -Depth 6
} finally {
    if ($null -ne $lockStream) { $lockStream.Dispose() }
}
