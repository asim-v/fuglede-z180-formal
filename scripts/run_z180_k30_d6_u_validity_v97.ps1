[CmdletBinding()]
param(
    [switch]$ApplyIntegrationPatch,
    [switch]$StaticCheckOnly,
    [uint64]$MemoryCapBytes = 3489660928
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$expectedCapBytes = [uint64]3489660928
$expectedGeneratorSha = '03efd3842f746b000b550ef7fb0cf8722660a6fd0ea332ed4a6494266424a94b'
$expectedPhaseRunnerSha = 'c0cd9fc0be5f9234355000a74c6e331219f74e1994c502bbd08b25797633d59f'
$authoredManifestSha = 'a3067768be1032f81c3cde55dc233f6e7dd210f0168f6369b55cf1b9c9523a57'
$integratedManifestSha = 'd4959f272f5dd7b23487f26d8c1decf257cea78b4e06557935ab8fd8759e96cc'
$legacyDataSha = '78e3372ff7b722e64963c45d02e5ae023188ad14b75630ae7b4bcd3afda1f115'
$integratedDataSha = '17d5a88f59df0eeae64b157ae83c1abcc835847806002bf77f05df9c21432ceb'
$stateSchema = 'z180-k30-d6-u-validity-v97-serial-state-v1'
$policySchema = 'z180-k30-d6-u-validity-v97-runner-policy-v1'

$scriptPath = $MyInvocation.MyCommand.Path
$scriptRoot = Split-Path -Parent $scriptPath
$workspaceRoot = Split-Path -Parent $scriptRoot
$leanRoot = Join-Path $workspaceRoot 'fuglede_lean'
$generatorPath = Join-Path $leanRoot 'scripts\generate_z180_k30_d6_u_validity_v97.py'
$validityManifestPath = Join-Path $leanRoot 'generated\z180_k30_d6_u_validity_v97.manifest.json'
$dataPath = Join-Path $leanRoot 'Fuglede\Z180K30ExceptionalProjectiveProfileDataV97D6.lean'
$divisorPath = Join-Path $leanRoot 'Fuglede\Z180K30ExceptionalProjectiveProfileDivisorV97D6.lean'
$phaseRunner = Join-Path $scriptRoot 'run_z180_k30_projective_cap20_pilot_v89.ps1'
$policyPath = Join-Path $scriptRoot 'run_z180_k30_d6_u_validity_v97.manifest.json'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_d6_u_validity_v97'
$sharedTelemetryRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_v89_batch'
$statePath = Join-Path $auditRoot 'state.json'
$pausePath = Join-Path $auditRoot 'pause.request'
$utf8NoBom = [System.Text.UTF8Encoding]::new($false, $true)

function Get-Sha256Lower {
    param([Parameter(Mandatory = $true)][string]$Path)
    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        throw "Missing authenticated file: $Path"
    }
    return (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-TextSha256Lower {
    param([Parameter(Mandatory = $true)][string]$Text)
    $sha = [System.Security.Cryptography.SHA256]::Create()
    try {
        $bytes = $utf8NoBom.GetBytes($Text)
        return ([System.BitConverter]::ToString($sha.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant()
    } finally {
        $sha.Dispose()
    }
}

function Assert-Equal {
    param(
        [Parameter(Mandatory = $true)]$Actual,
        [Parameter(Mandatory = $true)]$Expected,
        [Parameter(Mandatory = $true)][string]$Label
    )
    if ($Actual -cne $Expected) {
        throw "$Label mismatch: actual=$Actual expected=$Expected"
    }
}

function Assert-FileHash {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Expected,
        [Parameter(Mandatory = $true)][string]$Label
    )
    Assert-Equal (Get-Sha256Lower $Path) $Expected.ToLowerInvariant() $Label
}

function Get-OccurrenceCount {
    param(
        [Parameter(Mandatory = $true)][string]$Text,
        [Parameter(Mandatory = $true)][string]$Needle
    )
    if ($Needle.Length -eq 0) {
        throw 'Cannot count an empty authenticated needle.'
    }
    $count = 0
    $offset = 0
    while ($true) {
        $index = $Text.IndexOf($Needle, $offset, [System.StringComparison]::Ordinal)
        if ($index -lt 0) {
            break
        }
        $count += 1
        $offset = $index + $Needle.Length
    }
    return $count
}

function Get-LegacyValidityBlock {
    $lines = @(
        'theorem z180_k30_projective_u_profiles_valid_v97_d6 :',
        '    projectiveUProfilesValidB_v97 6',
        '      z180K30ProjectiveUProfilesV97D6 = true := by',
        '  simp [projectiveUProfilesValidB_v97, z180K30ProjectiveUProfilesV97D6]'
    )
    return (($lines -join "`n") + "`n`n")
}

function Get-IntegratedCandidates {
    param(
        [Parameter(Mandatory = $true)][string]$DataText,
        [Parameter(Mandatory = $true)][string]$ManifestText
    )
    $legacyBlock = Get-LegacyValidityBlock
    Assert-Equal (Get-OccurrenceCount $DataText $legacyBlock) 1 'legacy validity theorem block count'
    $dataCandidate = $DataText.Replace($legacyBlock, '')
    $endpointReplacements = [ordered]@{
        'import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6UAggregate' =
            'import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97'
        'import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VAggregate' =
            'import Fuglede.Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97'
        '  exact z180_k30_projective_profile_members_complete_v97_d6_u' =
            '  exact z180_k30_projective_d6_u_complete_algebraic_pilot_v97'
        '  exact z180_k30_projective_profile_members_complete_v97_d6_v' =
            '  exact z180_k30_projective_d6_v_complete_algebraic_pilot_v97'
    }
    foreach ($replacement in $endpointReplacements.GetEnumerator()) {
        Assert-Equal (Get-OccurrenceCount $dataCandidate ([string]$replacement.Key)) 1 `
            "legacy DataD6 endpoint occurrence: $($replacement.Key)"
        Assert-Equal (Get-OccurrenceCount $dataCandidate ([string]$replacement.Value)) 0 `
            "premature algebraic DataD6 endpoint occurrence: $($replacement.Value)"
        $dataCandidate = $dataCandidate.Replace(
            [string]$replacement.Key,
            [string]$replacement.Value
        )
    }
    Assert-Equal (Get-TextSha256Lower $dataCandidate) $integratedDataSha `
        'post-removal/algebraic-endpoint DataD6 SHA256'

    $dataInputPath = 'Fuglede/Z180K30ExceptionalProjectiveProfileDataV97D6.lean'
    $oldInputLine = '    "' + $dataInputPath + '": "' + $legacyDataSha + '",'
    $newInputLine = '    "' + $dataInputPath + '": "' + $integratedDataSha + '",'
    Assert-Equal (Get-OccurrenceCount $ManifestText $oldInputLine) 1 'authored manifest DataD6 pin count'
    Assert-Equal (Get-OccurrenceCount $ManifestText $newInputLine) 0 'premature integrated manifest DataD6 pin count'
    $manifestCandidate = $ManifestText.Replace($oldInputLine, $newInputLine)
    Assert-Equal (Get-TextSha256Lower $manifestCandidate) $integratedManifestSha `
        'post-removal/algebraic-endpoint validity manifest SHA256'

    return [pscustomobject]@{
        dataText = $dataCandidate
        manifestText = $manifestCandidate
    }
}

function Read-JsonFile {
    param([Parameter(Mandatory = $true)][string]$Path)
    return ([System.IO.File]::ReadAllText($Path, $utf8NoBom) | ConvertFrom-Json)
}

function Invoke-GeneratorCheck {
    $python = Get-Command python -ErrorAction Stop
    $output = @(& $python.Source $generatorPath --check 2>&1)
    if ($LASTEXITCODE -ne 0) {
        throw "D6 U-validity generator authentication failed: $($output -join [Environment]::NewLine)"
    }
    if (($output -join "`n") -notmatch 'checked 131 Lean files; members=2306; leaves=119; max_leaf=20; classes=10') {
        throw "Unexpected D6 U-validity generator report: $($output -join [Environment]::NewLine)"
    }
}

function Assert-Policy {
    Assert-FileHash $generatorPath $expectedGeneratorSha 'validity generator SHA256'
    Assert-FileHash $phaseRunner $expectedPhaseRunnerSha 'isolated phase runner SHA256'
    $policy = Read-JsonFile $policyPath
    Assert-Equal ([string]$policy.schema) $policySchema 'runner policy schema'
    Assert-Equal ([uint64]$policy.memoryCapBytes) $expectedCapBytes 'runner policy memory cap'
    Assert-Equal ([string]$policy.generatorSha256) $expectedGeneratorSha 'runner policy generator SHA256'
    Assert-Equal ([string]$policy.phaseRunnerSha256) $expectedPhaseRunnerSha 'runner policy phase-runner SHA256'
    Assert-Equal ([string]$policy.authoredManifestSha256) $authoredManifestSha 'runner policy authored manifest SHA256'
    Assert-Equal ([string]$policy.integratedManifestSha256) $integratedManifestSha 'runner policy integrated manifest SHA256'
    Assert-Equal ([string]$policy.legacyDataSha256) $legacyDataSha 'runner policy legacy DataD6 SHA256'
    Assert-Equal ([string]$policy.integratedDataSha256) $integratedDataSha 'runner policy integrated DataD6 SHA256'
    Assert-Equal ([int]$policy.moduleCount) 131 'runner policy module count'
    Assert-Equal ([int]$policy.buildCount) 131 'runner policy build count'
    Assert-Equal ([int]$policy.checkerCount) 12 'runner policy checker count'
    Assert-Equal ([string]$policy.runner) 'scripts/run_z180_k30_d6_u_validity_v97.ps1' 'runner policy path'
    Assert-Equal ([string]$policy.phaseRunner) 'scripts/run_z180_k30_projective_cap20_pilot_v89.ps1' 'phase-runner policy path'
    Assert-Equal ([string]$policy.generator) 'fuglede_lean/scripts/generate_z180_k30_d6_u_validity_v97.py' 'generator policy path'
    Assert-Equal ([string]$policy.validityManifest) 'fuglede_lean/generated/z180_k30_d6_u_validity_v97.manifest.json' 'validity-manifest policy path'
    Assert-Equal ([string]$policy.canonicalData) 'fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveProfileDataV97D6.lean' 'canonical-Data policy path'
    Assert-FileHash $scriptPath ([string]$policy.runnerSha256) 'serial runner SHA256'
    return $policy
}

function Get-ManifestOutputMap {
    param([Parameter(Mandatory = $true)]$Manifest)
    $map = [System.Collections.Generic.Dictionary[string, string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($property in $Manifest.outputs.PSObject.Properties) {
        $name = [string]$property.Name
        if ($map.ContainsKey($name)) {
            throw "Duplicate output hash entry: $($property.Name)"
        }
        $map.Add($name, ([string]$property.Value).ToLowerInvariant())
    }
    return $map
}

function Convert-FileToModule {
    param([Parameter(Mandatory = $true)][string]$File)
    return (($File -replace '\.lean$', '') -replace '/', '.')
}

function Get-OleanPath {
    param([Parameter(Mandatory = $true)][string]$Module)
    return Join-Path $leanRoot ('.lake\build\lib\lean\' + $Module.Replace('.', '\') + '.olean')
}

function Assert-ManifestTopology {
    param([Parameter(Mandatory = $true)]$Manifest)
    Assert-Equal ([string]$Manifest.schema) 'z180-k30-d6-u-validity-v97/1' 'validity manifest schema'
    Assert-Equal ([int]$Manifest.invariants.generated_output_count) 131 'validity output count'
    Assert-Equal ([int]$Manifest.invariants.u_leaf_count) 119 'validity leaf count'
    Assert-Equal ([int]$Manifest.invariants.u_maximum_members_per_leaf) 20 'validity maximum leaf size'
    Assert-Equal ([int]$Manifest.invariants.u_class_count) 10 'validity class count'
    if (-not [bool]$Manifest.invariants.legacy_monolithic_validity_theorem_must_be_removed_before_compile) {
        throw 'Validity manifest no longer records its DataD6 integration precondition.'
    }

    $stages = @($Manifest.compile_stages)
    Assert-Equal $stages.Count 4 'validity compile-stage count'
    $expectedKinds = @(
        'core',
        'profile_aligned_max20_leaves',
        'ten_class_structural_aggregates',
        'exact_outer_validity_aggregate'
    )
    $expectedCounts = @(1, 119, 10, 1)
    $outputMap = Get-ManifestOutputMap $Manifest
    Assert-Equal $outputMap.Count 131 'validity output-hash count'
    $entries = [System.Collections.ArrayList]::new()
    $seenFiles = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    $seenModules = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )

    for ($stageIndex = 0; $stageIndex -lt $stages.Count; $stageIndex += 1) {
        $stage = $stages[$stageIndex]
        Assert-Equal ([int]$stage.stage) ($stageIndex + 1) "validity stage $stageIndex number"
        Assert-Equal ([string]$stage.kind) $expectedKinds[$stageIndex] "validity stage $stageIndex kind"
        $files = @($stage.files)
        Assert-Equal $files.Count $expectedCounts[$stageIndex] "validity stage $stageIndex file count"
        for ($fileIndex = 0; $fileIndex -lt $files.Count; $fileIndex += 1) {
            $file = [string]$files[$fileIndex]
            if (-not $seenFiles.Add($file)) {
                throw "Duplicate compile file: $file"
            }
            if (-not $outputMap.ContainsKey($file)) {
                throw "Compile file lacks an authenticated output hash: $file"
            }
            $module = Convert-FileToModule $file
            if (-not $seenModules.Add($module)) {
                throw "Duplicate compile module: $module"
            }
            $sourcePath = Join-Path $leanRoot ($file.Replace('/', '\'))
            Assert-FileHash $sourcePath $outputMap[$file] "source SHA256 for $module"
            [void]$entries.Add([pscustomobject]@{
                file = $file
                module = $module
                kind = [string]$stage.kind
                sourcePath = $sourcePath
                sourceSha256 = $outputMap[$file]
                checker = ($stageIndex -ne 1)
            })
        }
    }

    $coreFile = 'Fuglede/Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97.lean'
    $aggregateFile = 'Fuglede/Z180K30ExceptionalProjectiveProfileD6UValidityAggregatePilotV97.lean'
    Assert-Equal ([string]$entries[0].file) $coreFile 'core compile file'
    Assert-Equal ([string]$entries[$entries.Count - 1].file) $aggregateFile 'aggregate compile file'
    $leafEntries = @($entries | Where-Object { $_.kind -ceq 'profile_aligned_max20_leaves' })
    foreach ($leaf in $leafEntries) {
        if ([string]$leaf.file -cnotmatch '^Fuglede/Z180K30ExceptionalProjectiveProfileD6UValidityLeafU\d{2}C\d{2}PilotV97\.lean$') {
            throw "Malformed bounded validity leaf path: $($leaf.file)"
        }
        if ([bool]$leaf.checker) {
            throw "Validity leaf unexpectedly requests a checker: $($leaf.file)"
        }
    }
    $groupEntries = @($entries | Where-Object { $_.kind -ceq 'ten_class_structural_aggregates' })
    for ($group = 0; $group -lt 10; $group += 1) {
        $expectedGroup = 'Fuglede/Z180K30ExceptionalProjectiveProfileD6UValidityGroupU{0:D2}PilotV97.lean' -f $group
        Assert-Equal ([string]$groupEntries[$group].file) $expectedGroup "validity group U$('{0:D2}' -f $group) path"
        if (-not [bool]$groupEntries[$group].checker) {
            throw "Validity group lacks its required checker: $expectedGroup"
        }
    }
    Assert-Equal @($entries | Where-Object checker).Count 12 'checker module count'
    return @($entries)
}

function Assert-DataState {
    param([Parameter(Mandatory = $true)][string]$ManifestSha)
    $dataSha = Get-Sha256Lower $dataPath
    $dataText = [System.IO.File]::ReadAllText($dataPath, $utf8NoBom)
    $legacyBlock = Get-LegacyValidityBlock
    $theoremPattern = '(?m)^theorem z180_k30_projective_u_profiles_valid_v97_d6\s*:'
    $definitionPattern = '(?m)^def z180K30ProjectiveUProfilesV97D6\s*:'
    Assert-Equal ([regex]::Matches($dataText, $definitionPattern).Count) 1 'canonical DataD6 U-profile definition count'

    if ($ManifestSha -ceq $authoredManifestSha) {
        Assert-Equal $dataSha $legacyDataSha 'authored DataD6 SHA256'
        Assert-Equal (Get-OccurrenceCount $dataText $legacyBlock) 1 'authored legacy theorem block count'
        Assert-Equal ([regex]::Matches($dataText, $theoremPattern).Count) 1 'authored legacy theorem declaration count'
    } elseif ($ManifestSha -ceq $integratedManifestSha) {
        Assert-Equal $dataSha $integratedDataSha 'integrated DataD6 SHA256'
        Assert-Equal (Get-OccurrenceCount $dataText $legacyBlock) 0 'integrated legacy theorem block count'
        Assert-Equal ([regex]::Matches($dataText, $theoremPattern).Count) 0 'integrated legacy theorem declaration count'
    } else {
        throw "Unsupported validity manifest SHA256: $ManifestSha"
    }
}

function Invoke-AtomicIntegrationPatch {
    Assert-FileHash $validityManifestPath $authoredManifestSha 'pre-integration validity manifest SHA256'
    Assert-FileHash $dataPath $legacyDataSha 'pre-integration DataD6 SHA256'
    $dataText = [System.IO.File]::ReadAllText($dataPath, $utf8NoBom)
    $manifestText = [System.IO.File]::ReadAllText($validityManifestPath, $utf8NoBom)
    $candidate = Get-IntegratedCandidates $dataText $manifestText

    $transaction = [Guid]::NewGuid().ToString('N')
    $dataTemp = "$dataPath.$transaction.tmp"
    $manifestTemp = "$validityManifestPath.$transaction.tmp"
    $dataBackup = "$dataPath.$transaction.rollback"
    $manifestBackup = "$validityManifestPath.$transaction.rollback"
    $dataReplaced = $false
    $manifestReplaced = $false
    try {
        [System.IO.File]::WriteAllText($dataTemp, [string]$candidate.dataText, $utf8NoBom)
        [System.IO.File]::WriteAllText($manifestTemp, [string]$candidate.manifestText, $utf8NoBom)
        Assert-FileHash $dataTemp $integratedDataSha 'staged integrated DataD6 SHA256'
        Assert-FileHash $manifestTemp $integratedManifestSha 'staged integrated manifest SHA256'
        Assert-FileHash $dataPath $legacyDataSha 'pre-commit DataD6 SHA256'
        Assert-FileHash $validityManifestPath $authoredManifestSha 'pre-commit validity manifest SHA256'

        [System.IO.File]::Replace($dataTemp, $dataPath, $dataBackup, $true)
        $dataReplaced = $true
        [System.IO.File]::Replace($manifestTemp, $validityManifestPath, $manifestBackup, $true)
        $manifestReplaced = $true

        Assert-FileHash $dataPath $integratedDataSha 'committed integrated DataD6 SHA256'
        Assert-FileHash $validityManifestPath $integratedManifestSha 'committed integrated manifest SHA256'
        Assert-DataState $integratedManifestSha
        Invoke-GeneratorCheck

        Remove-Item -LiteralPath $dataBackup, $manifestBackup -Force -ErrorAction SilentlyContinue
        Write-Output "INTEGRATED data=$integratedDataSha manifest=$integratedManifestSha"
    } catch {
        $integrationError = $_
        $rollbackErrors = [System.Collections.ArrayList]::new()
        try {
            if ($manifestReplaced -and (Test-Path -LiteralPath $manifestBackup -PathType Leaf)) {
                $currentManifestHash = Get-Sha256Lower $validityManifestPath
                if ($currentManifestHash -ceq $integratedManifestSha) {
                    [System.IO.File]::Replace($manifestBackup, $validityManifestPath, $manifestTemp, $true)
                } elseif ($currentManifestHash -cne $authoredManifestSha) {
                    throw "refusing to overwrite external manifest drift $currentManifestHash"
                }
            }
        } catch {
            [void]$rollbackErrors.Add("manifest rollback: $($_.Exception.Message)")
        }
        try {
            if ($dataReplaced -and (Test-Path -LiteralPath $dataBackup -PathType Leaf)) {
                $currentDataHash = Get-Sha256Lower $dataPath
                if ($currentDataHash -ceq $integratedDataSha) {
                    [System.IO.File]::Replace($dataBackup, $dataPath, $dataTemp, $true)
                } elseif ($currentDataHash -cne $legacyDataSha) {
                    throw "refusing to overwrite external DataD6 drift $currentDataHash"
                }
            }
        } catch {
            [void]$rollbackErrors.Add("DataD6 rollback: $($_.Exception.Message)")
        }
        try {
            Assert-FileHash $dataPath $legacyDataSha 'rolled-back DataD6 SHA256'
            Assert-FileHash $validityManifestPath $authoredManifestSha 'rolled-back validity manifest SHA256'
        } catch {
            [void]$rollbackErrors.Add("rollback authentication: $($_.Exception.Message)")
        }
        foreach ($temporary in @($dataTemp, $manifestTemp)) {
            Remove-Item -LiteralPath $temporary -Force -ErrorAction SilentlyContinue
        }
        $rollbackDetail = if ($rollbackErrors.Count -eq 0) {
            Remove-Item -LiteralPath $dataBackup, $manifestBackup -Force -ErrorAction SilentlyContinue
            'rollback authenticated'
        } else {
            ($rollbackErrors -join '; ') + "; recovery files retained at $dataBackup and $manifestBackup"
        }
        throw "Atomic D6 validity integration failed ($rollbackDetail): $($integrationError.Exception.Message)"
    } finally {
        foreach ($temporary in @($dataTemp, $manifestTemp)) {
            Remove-Item -LiteralPath $temporary -Force -ErrorAction SilentlyContinue
        }
    }
}

function Assert-SerialWindowFree {
    $active = @(Get-CimInstance Win32_Process | Where-Object {
        $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe')
    })
    if ($active.Count -ne 0) {
        $detail = ($active | ForEach-Object {
            '{0}:{1}' -f $_.Name, $_.ProcessId
        }) -join ', '
        throw "Serial Lean window is not free for D6 validity replay: $detail"
    }
}

function Save-State {
    param(
        [Parameter(Mandatory = $true)][string]$DriverSha,
        [Parameter(Mandatory = $true)][AllowEmptyCollection()]
        [System.Collections.Generic.HashSet[string]]$Completed,
        [Parameter(Mandatory = $true)][AllowEmptyCollection()]
        [System.Collections.ArrayList]$Records,
        [Parameter(Mandatory = $true)][string]$StartedAtUtc
    )
    $state = [ordered]@{
        schema = $stateSchema
        manifestSha256 = $integratedManifestSha
        generatorSha256 = $expectedGeneratorSha
        phaseRunnerSha256 = $expectedPhaseRunnerSha
        driverSha256 = $DriverSha
        dataSha256 = $integratedDataSha
        memoryCapBytes = $expectedCapBytes
        startedAtUtc = $StartedAtUtc
        updatedAtUtc = [DateTime]::UtcNow.ToString('o')
        completedModules = @($Completed | Sort-Object)
        records = @($Records)
    }
    $json = $state | ConvertTo-Json -Depth 10
    $temporary = "$statePath.$([Guid]::NewGuid().ToString('N')).tmp"
    [System.IO.File]::WriteAllText($temporary, $json + "`n", $utf8NoBom)
    if (Test-Path -LiteralPath $statePath -PathType Leaf) {
        $backup = "$statePath.$([Guid]::NewGuid().ToString('N')).bak"
        [System.IO.File]::Replace($temporary, $statePath, $backup, $true)
        Remove-Item -LiteralPath $backup -Force -ErrorAction SilentlyContinue
    } else {
        [System.IO.File]::Move($temporary, $statePath)
    }
}

function Get-TelemetryPath {
    param(
        [Parameter(Mandatory = $true)][string]$Module,
        [Parameter(Mandatory = $true)][ValidateSet('build', 'checker')][string]$Phase
    )
    $safeModule = $Module -replace '[^A-Za-z0-9_.-]', '_'
    return Join-Path $sharedTelemetryRoot "$safeModule.$Phase.json"
}

function Invoke-IsolatedPhase {
    param(
        [Parameter(Mandatory = $true)][string]$Module,
        [Parameter(Mandatory = $true)][ValidateSet('build', 'checker')][string]$Phase
    )
    Assert-FileHash $phaseRunner $expectedPhaseRunnerSha 'isolated phase runner SHA256 before launch'
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
    Assert-Equal ([string]$result.module) $Module "telemetry module for $Phase"
    Assert-Equal ([string]$result.phase) $Phase "telemetry phase for $Module"
    Assert-Equal ([uint64]$result.capBytes) $expectedCapBytes "telemetry cap for $Module $Phase"
    if ($exitCode -ne 0 -or [string]$result.status -cne 'passed') {
        throw "Phase failed for $Module $Phase`: status=$($result.status), detail=$($result.detail)"
    }
    $telemetryPath = Get-TelemetryPath $Module $Phase
    return [pscustomobject]@{
        result = $result
        telemetryPath = $telemetryPath
        telemetrySha256 = Get-Sha256Lower $telemetryPath
    }
}

function Assert-ResumeState {
    param(
        [Parameter(Mandatory = $true)]$State,
        [Parameter(Mandatory = $true)][string]$DriverSha,
        [Parameter(Mandatory = $true)][object[]]$Entries
    )
    Assert-Equal ([string]$State.schema) $stateSchema 'resume state schema'
    Assert-Equal ([string]$State.manifestSha256) $integratedManifestSha 'resume manifest SHA256'
    Assert-Equal ([string]$State.generatorSha256) $expectedGeneratorSha 'resume generator SHA256'
    Assert-Equal ([string]$State.phaseRunnerSha256) $expectedPhaseRunnerSha 'resume phase-runner SHA256'
    Assert-Equal ([string]$State.driverSha256) $DriverSha 'resume driver SHA256'
    Assert-Equal ([string]$State.dataSha256) $integratedDataSha 'resume DataD6 SHA256'
    Assert-Equal ([uint64]$State.memoryCapBytes) $expectedCapBytes 'resume memory cap'

    $entryMap = [System.Collections.Generic.Dictionary[string, object]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($entry in $Entries) {
        [void]$entryMap.Add([string]$entry.module, $entry)
    }
    $completedSeen = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    $records = @($State.records)
    foreach ($moduleObject in @($State.completedModules)) {
        $module = [string]$moduleObject
        if (-not $completedSeen.Add($module)) {
            throw "Duplicate completed module in resume state: $module"
        }
        if (-not $entryMap.ContainsKey($module)) {
            throw "Resume state contains a module outside the manifest: $module"
        }
        $entry = $entryMap[$module]
        Assert-FileHash ([string]$entry.sourcePath) ([string]$entry.sourceSha256) "resume source SHA256 for $module"
        $oleanPath = Get-OleanPath $module
        if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            throw "Missing completed .olean during resume: $oleanPath"
        }
        $buildRecords = @($records | Where-Object {
            [string]$_.module -ceq $module -and [string]$_.phase -ceq 'build'
        })
        Assert-Equal $buildRecords.Count 1 "resume build-record count for $module"
        Assert-Equal (Get-Sha256Lower $oleanPath) ([string]$buildRecords[0].oleanSha256) "resume .olean SHA256 for $module"
        $checkerRecords = @($records | Where-Object {
            [string]$_.module -ceq $module -and [string]$_.phase -ceq 'checker'
        })
        $expectedCheckerRecords = if ([bool]$entry.checker) { 1 } else { 0 }
        Assert-Equal $checkerRecords.Count $expectedCheckerRecords "resume checker-record count for $module"
    }
    foreach ($record in $records) {
        $recordModule = [string]$record.module
        if (-not $completedSeen.Contains($recordModule)) {
            throw "Resume record exists for an incomplete module: $recordModule"
        }
        $recordPhase = [string]$record.phase
        if ($recordPhase -notin @('build', 'checker')) {
            throw "Unsupported resume phase $recordPhase for $recordModule"
        }
        Assert-Equal ([string]$record.status) 'passed' "resume status for $recordModule $recordPhase"
        Assert-Equal ([uint64]$record.capBytes) $expectedCapBytes "resume cap for $recordModule $recordPhase"
        Assert-FileHash ([string]$record.telemetryPath) ([string]$record.telemetrySha256) "resume telemetry SHA256 for $recordModule $recordPhase"
    }
    $foundGap = $false
    foreach ($entry in $Entries) {
        $module = [string]$entry.module
        if ($completedSeen.Contains($module)) {
            if ($foundGap) {
                throw "Resume state is not a topological prefix at $module"
            }
        } else {
            $foundGap = $true
        }
    }
}

if ($MemoryCapBytes -ne $expectedCapBytes) {
    throw "D6 validity replay requires the exact 3.25 GiB cap $expectedCapBytes; got $MemoryCapBytes"
}

$policy = Assert-Policy
$driverSha = Get-Sha256Lower $scriptPath
$currentManifestSha = Get-Sha256Lower $validityManifestPath
if ($currentManifestSha -notin @($authoredManifestSha, $integratedManifestSha)) {
    throw "Validity manifest is neither authored nor fully integrated: $currentManifestSha"
}
Assert-DataState $currentManifestSha
$manifest = Read-JsonFile $validityManifestPath
$entries = Assert-ManifestTopology $manifest
Invoke-GeneratorCheck

if ($StaticCheckOnly) {
    if ($ApplyIntegrationPatch) {
        throw '-StaticCheckOnly never accepts -ApplyIntegrationPatch.'
    }
    if ($currentManifestSha -ceq $authoredManifestSha) {
        $dataText = [System.IO.File]::ReadAllText($dataPath, $utf8NoBom)
        $manifestText = [System.IO.File]::ReadAllText($validityManifestPath, $utf8NoBom)
        [void](Get-IntegratedCandidates $dataText $manifestText)
        $stateName = 'authored-pre-integration'
    } else {
        $stateName = 'integrated-ready'
    }
    [ordered]@{
        status = 'source-ready'
        state = $stateName
        manifestSha256 = $currentManifestSha
        expectedIntegratedManifestSha256 = $integratedManifestSha
        expectedIntegratedDataSha256 = $integratedDataSha
        modules = $entries.Count
        builds = $entries.Count
        checkers = @($entries | Where-Object checker).Count
        memoryCapBytes = $expectedCapBytes
        leanWasRun = $false
    } | ConvertTo-Json -Compress
    exit 0
}

Assert-SerialWindowFree
if ($currentManifestSha -ceq $authoredManifestSha) {
    if (-not $ApplyIntegrationPatch) {
        throw 'Aggregate is blocked by the legacy DataD6 validity theorem. Re-run with -ApplyIntegrationPatch for the authenticated two-file transaction.'
    }
    Invoke-AtomicIntegrationPatch
    $currentManifestSha = Get-Sha256Lower $validityManifestPath
    Assert-Equal $currentManifestSha $integratedManifestSha 'post-transaction validity manifest SHA256'
    $manifest = Read-JsonFile $validityManifestPath
    $entries = Assert-ManifestTopology $manifest
} elseif ($ApplyIntegrationPatch) {
    Write-Output 'INTEGRATION-ALREADY-PRESENT'
}

Assert-FileHash $dataPath $integratedDataSha 'pre-Lean integrated DataD6 SHA256'
Assert-FileHash $validityManifestPath $integratedManifestSha 'pre-Lean validity manifest SHA256'
Assert-FileHash $divisorPath ([string]$manifest.inputs.'Fuglede/Z180K30ExceptionalProjectiveProfileDivisorV97D6.lean') 'pre-Lean untouched Divisor SHA256'
Assert-DataState $integratedManifestSha
Invoke-GeneratorCheck
Assert-SerialWindowFree

New-Item -ItemType Directory -Path $auditRoot, $sharedTelemetryRoot -Force | Out-Null
$completed = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$records = [System.Collections.ArrayList]::new()
$startedAtUtc = [DateTime]::UtcNow.ToString('o')
if (Test-Path -LiteralPath $statePath -PathType Leaf) {
    $oldState = Read-JsonFile $statePath
    Assert-ResumeState $oldState $driverSha $entries
    foreach ($module in @($oldState.completedModules)) {
        [void]$completed.Add([string]$module)
    }
    foreach ($record in @($oldState.records)) {
        [void]$records.Add($record)
    }
    $startedAtUtc = [string]$oldState.startedAtUtc
} else {
    Save-State $driverSha $completed $records $startedAtUtc
}

foreach ($entry in $entries) {
    $module = [string]$entry.module
    if ($completed.Contains($module)) {
        continue
    }
    if (Test-Path -LiteralPath $pausePath -PathType Leaf) {
        Remove-Item -LiteralPath $pausePath -Force
        Save-State $driverSha $completed $records $startedAtUtc
        Write-Output "PAUSED completed=$($completed.Count)/131 next=$module"
        exit 0
    }

    Assert-FileHash ([string]$entry.sourcePath) ([string]$entry.sourceSha256) "pre-build source SHA256 for $module"
    Assert-FileHash $validityManifestPath $integratedManifestSha "pre-build manifest SHA256 for $module"
    Assert-FileHash $dataPath $integratedDataSha "pre-build DataD6 SHA256 for $module"
    $build = Invoke-IsolatedPhase -Module $module -Phase build
    $oleanPath = Get-OleanPath $module
    if (-not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
        throw "Build passed without producing the expected .olean: $oleanPath"
    }
    $oleanSha = Get-Sha256Lower $oleanPath
    [void]$records.Add([ordered]@{
        module = $module
        kind = [string]$entry.kind
        phase = 'build'
        status = 'passed'
        capBytes = $expectedCapBytes
        peakBytes = [uint64]$build.result.maxLeanWorkingSetBytes
        sourceSha256 = [string]$entry.sourceSha256
        oleanPath = $oleanPath
        oleanSha256 = $oleanSha
        telemetryPath = [string]$build.telemetryPath
        telemetrySha256 = [string]$build.telemetrySha256
        completedAtUtc = [string]$build.result.completedAtUtc
    })

    if ([bool]$entry.checker) {
        $checker = Invoke-IsolatedPhase -Module $module -Phase checker
        Assert-Equal (Get-Sha256Lower $oleanPath) $oleanSha "post-checker .olean SHA256 for $module"
        [void]$records.Add([ordered]@{
            module = $module
            kind = [string]$entry.kind
            phase = 'checker'
            status = 'passed'
            capBytes = $expectedCapBytes
            peakBytes = [uint64]$checker.result.maxLeanWorkingSetBytes
            sourceSha256 = [string]$entry.sourceSha256
            oleanPath = $oleanPath
            oleanSha256 = $oleanSha
            telemetryPath = [string]$checker.telemetryPath
            telemetrySha256 = [string]$checker.telemetrySha256
            completedAtUtc = [string]$checker.result.completedAtUtc
        })
    }

    [void]$completed.Add($module)
    Save-State $driverSha $completed $records $startedAtUtc
    if (($completed.Count % 20) -eq 0 -or $completed.Count -eq 1) {
        Write-Output "MILESTONE completed=$($completed.Count)/131 module=$module"
    }
}

Assert-Equal $completed.Count 131 'final completed-module count'
Assert-Equal $records.Count 143 'final phase-record count'
Write-Output "COMPLETE completed=131/131 checkers=12 manifest=$integratedManifestSha driver=$driverSha"
