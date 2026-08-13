[CmdletBinding()]
param(
    [uint64]$MemoryCapBytes = 3489660928
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$generatorPath = Join-Path $leanRoot 'scripts\generate_z180_k30_d6_algebraic_v97.py'
$manifestPath = Join-Path $leanRoot 'generated\z180_k30_d6_algebraic_v97.manifest.json'
$phaseRunner = Join-Path $scriptRoot 'run_z180_k30_projective_cap20_pilot_v89.ps1'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_d6_algebraic_v97'
$statePath = Join-Path $auditRoot 'state.json'
$pausePath = Join-Path $auditRoot 'pause.request'
$preBridgeModule =
    'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicLeaf314PilotV97'
$transitionManifestSha =
    '89ffe0f277b2ba75927154209086ba1dd2c8d58bd26ce56f850e256e94cb1fc8'
$transitionGeneratorSha =
    '442f111a07fe80cc11783b19651569cfa4f1be59c55fd38c9e8007ad9b79cda9'

New-Item -ItemType Directory -Path $auditRoot -Force | Out-Null

function Convert-FileToModule {
    param([string]$File)
    return (($File -replace '\.lean$', '') -replace '/', '.')
}

function Save-State {
    param(
        [string]$ManifestSha,
        [System.Collections.Generic.HashSet[string]]$Completed,
        [System.Collections.ArrayList]$Records,
        [string]$StartedAtUtc
    )
    $state = [ordered]@{
        schema = 'z180-k30-d6-algebraic-v97-serial-state-v1'
        manifestSha256 = $ManifestSha
        startedAtUtc = $StartedAtUtc
        updatedAtUtc = [DateTime]::UtcNow.ToString('o')
        completedModules = @($Completed | Sort-Object)
        records = @($Records)
    }
    $temporary = "$statePath.tmp"
    $state | ConvertTo-Json -Depth 8 |
        Set-Content -LiteralPath $temporary -Encoding UTF8
    Move-Item -LiteralPath $temporary -Destination $statePath -Force
}

function Invoke-IsolatedPhase {
    param(
        [string]$Module,
        [ValidateSet('build', 'checker')]
        [string]$Phase
    )
    $output = @(& powershell.exe -NoProfile -ExecutionPolicy Bypass `
        -File $phaseRunner -Module $Module -Phase $Phase `
        -MemoryCapBytes $MemoryCapBytes 2>&1)
    $exitCode = $LASTEXITCODE
    $jsonLines = @($output | Where-Object {
        ([string]$_).TrimStart().StartsWith('{')
    })
    if ($jsonLines.Count -eq 0) {
        throw "No telemetry for $Module $Phase`: $($output -join [Environment]::NewLine)"
    }
    $result = ([string]$jsonLines[-1]) | ConvertFrom-Json
    if ($exitCode -ne 0 -or [string]$result.status -ne 'passed') {
        throw "Phase failed for $Module $Phase`: status=$($result.status), detail=$($result.detail)"
    }
    return $result
}

$active = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe')
})
if ($active.Count -ne 0) {
    throw 'Serial Lean window is not free for D6 algebraic replay.'
}

$manifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$manifestSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()
$generatorSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $generatorPath).Hash.ToLowerInvariant()
$preloadedState = $null
if (Test-Path -LiteralPath $statePath -PathType Leaf) {
    $preloadedState = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
}
$transitionMode = (
    $manifestSha -eq $transitionManifestSha -and
    $null -ne $preloadedState -and
    [string]$preloadedState.manifestSha256 -eq $transitionManifestSha -and
    $generatorSha -eq $transitionGeneratorSha
)
if (-not $transitionMode) {
    & python $generatorPath --check
    if ($LASTEXITCODE -ne 0) {
        throw "D6 generator authentication failed with exit code $LASTEXITCODE"
    }
}
$stages = @($manifest.compile_stages)
$modules = @(
    foreach ($stage in $stages) {
        foreach ($file in @($stage.files)) {
            [pscustomobject]@{
                module = Convert-FileToModule ([string]$file)
                kind = [string]$stage.kind
            }
        }
    }
)
if ($modules.Count -ne 585) {
    throw "Unexpected D6 compile count: $($modules.Count)"
}
$moduleNames = @($modules | ForEach-Object { [string]$_.module })
$uniqueModules = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
foreach ($moduleName in $moduleNames) {
    if (-not $uniqueModules.Add($moduleName)) {
        throw "Duplicate D6 module in compile plan: $moduleName"
    }
}
if ($uniqueModules.Count -ne 585 -or $moduleNames[572] -ne $preBridgeModule -or
    $moduleNames[573] -ne
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow00PilotV97') {
    throw 'D6 compile topology or pre-Bridge ordinal drifted.'
}

$completed = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$records = [System.Collections.ArrayList]::new()
$startedAtUtc = [DateTime]::UtcNow.ToString('o')
if (Test-Path -LiteralPath $statePath -PathType Leaf) {
    $oldState = $preloadedState
    if ([string]$oldState.manifestSha256 -ne $manifestSha) {
        throw 'D6 state manifest hash mismatch; refusing an unauthenticated migration.'
    }
    foreach ($module in @($oldState.completedModules)) {
        [void]$completed.Add([string]$module)
    }
    foreach ($record in @($oldState.records)) {
        [void]$records.Add($record)
    }
    $startedAtUtc = [string]$oldState.startedAtUtc
} else {
    $sealedPilots = @(
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97',
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermB000PilotV97',
        'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicLeaf003PilotV97'
    )
    foreach ($module in $sealedPilots) {
        $telemetry = Join-Path $workspaceRoot `
            "audit\z180_k30_projective_v89_batch\$module.build.json"
        $olean = Join-Path $leanRoot `
            ('.lake\build\lib\lean\' + $module.Replace('.', '\') + '.olean')
        if (-not (Test-Path -LiteralPath $telemetry -PathType Leaf) -or
            -not (Test-Path -LiteralPath $olean -PathType Leaf)) {
            throw "Missing sealed pilot artifact for $module"
        }
        $result = Get-Content -Raw -LiteralPath $telemetry | ConvertFrom-Json
        if ([string]$result.status -ne 'passed') {
            throw "Sealed pilot telemetry is not passed for $module"
        }
        [void]$completed.Add($module)
        [void]$records.Add([ordered]@{
            module = $module
            phase = 'build'
            status = 'passed-before-driver'
            peakBytes = [uint64]$result.maxLeanWorkingSetBytes
            completedAtUtc = [string]$result.completedAtUtc
        })
    }
    Save-State $manifestSha $completed $records $startedAtUtc
}

if ($completed.Count -gt $modules.Count) {
    throw 'D6 completed state exceeds the compile plan.'
}
for ($index = 0; $index -lt $completed.Count; $index += 1) {
    if (-not $completed.Contains($moduleNames[$index])) {
        throw "D6 completed state is not the exact prefix at ordinal $index."
    }
}
if ($transitionMode) {
    if ($completed.Count -ge 573) {
        throw 'Pre-refresh transition mode is valid only before the Bridge boundary.'
    }
    foreach ($property in $manifest.inputs.PSObject.Properties) {
        $inputPath = Join-Path $leanRoot (
            ([string]$property.Name) -replace '/', '\'
        )
        $inputSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $inputPath).Hash.ToLowerInvariant()
        if ($inputSha -ne ([string]$property.Value).ToLowerInvariant()) {
            throw "D6 transition input drift: $($property.Name)"
        }
    }
    for ($index = 0; $index -le 572; $index += 1) {
        $moduleName = $moduleNames[$index]
        $key = ($moduleName -replace '\.', '/') + '.lean'
        $hashProperty = $manifest.outputs.PSObject.Properties[$key]
        if ($null -eq $hashProperty) {
            throw "D6 transition module absent from manifest: $moduleName"
        }
        $sourcePath = Join-Path $leanRoot ($key -replace '/', '\')
        $sourceSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash.ToLowerInvariant()
        if ($sourceSha -ne ([string]$hashProperty.Value).ToLowerInvariant()) {
            throw "D6 transition source drift: $moduleName"
        }
    }
}

$checkerKinds = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
foreach ($checkerKind in @(
    'core', 'nat_index_aggregate', 'u_bridge_aggregate', 'v_singleton'
)) {
    [void]$checkerKinds.Add($checkerKind)
}

foreach ($entry in $modules) {
    $module = [string]$entry.module
    $kind = [string]$entry.kind
    if ($completed.Contains($module)) {
        continue
    }
    if (Test-Path -LiteralPath $pausePath -PathType Leaf) {
        Remove-Item -LiteralPath $pausePath -Force
        Save-State $manifestSha $completed $records $startedAtUtc
        Write-Output "PAUSED completed=$($completed.Count) next=$module"
        exit 0
    }
    $build = Invoke-IsolatedPhase -Module $module -Phase build
    [void]$records.Add([ordered]@{
        module = $module
        phase = 'build'
        status = [string]$build.status
        peakBytes = [uint64]$build.maxLeanWorkingSetBytes
        completedAtUtc = [string]$build.completedAtUtc
    })
    if ($checkerKinds.Contains($kind)) {
        $checker = Invoke-IsolatedPhase -Module $module -Phase checker
        [void]$records.Add([ordered]@{
            module = $module
            phase = 'checker'
            status = [string]$checker.status
            peakBytes = [uint64]$checker.maxLeanWorkingSetBytes
            completedAtUtc = [string]$checker.completedAtUtc
        })
    }
    [void]$completed.Add($module)
    Save-State $manifestSha $completed $records $startedAtUtc
    if ($module -eq $preBridgeModule) {
        if ($completed.Count -ne 573) {
            throw "D6 native pre-Bridge boundary count is $($completed.Count), expected 573."
        }
        Write-Output "PAUSED-PREBRIDGE completed=573 next=$($moduleNames[573])"
        exit 0
    }
    if (($completed.Count % 50) -eq 0) {
        Write-Output "MILESTONE completed=$($completed.Count)/585 module=$module"
    }
}

Write-Output "COMPLETE completed=$($completed.Count)/585 manifest=$manifestSha"
