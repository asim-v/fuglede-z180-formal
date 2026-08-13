[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$generatorPath = Join-Path $scriptRoot 'generate_z180_k30_projective_profile_audit_v97.py'
$manifestPath = Join-Path $scriptRoot 'z180_k30_projective_profile_audit_v97.manifest.json'
$phaseRunner = Join-Path $scriptRoot 'run_z180_k30_projective_cap20_pilot_v89.ps1'
$auditRoot = Join-Path $workspaceRoot 'audit\z180_k30_projective_v97_batch'
$statePath = Join-Path $auditRoot 'state.json'
$pausePath = Join-Path $auditRoot 'pause.request'
$capBytes = [uint64]3489660928

New-Item -ItemType Directory -Path $auditRoot -Force | Out-Null

function Save-State {
    param(
        [string]$ManifestSha,
        [System.Collections.Generic.HashSet[string]]$Completed,
        [System.Collections.ArrayList]$Records,
        [string]$StartedAtUtc
    )
    $state = [ordered]@{
        schema = 'z180-k30-projective-profile-v97-serial-state-v1'
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
        -MemoryCapBytes $capBytes 2>&1)
    $exitCode = $LASTEXITCODE
    $jsonLines = @($output | Where-Object { ([string]$_).TrimStart().StartsWith('{') })
    if ($jsonLines.Count -eq 0) {
        throw ("Phase runner emitted no telemetry for {0} {1}: {2}" -f `
            $Module, $Phase, ($output -join [Environment]::NewLine))
    }
    $result = ([string]$jsonLines[-1]) | ConvertFrom-Json
    if ($exitCode -ne 0 -or [string]$result.status -ne 'passed') {
        throw ("Phase failed for {0} {1}: status={2}, detail={3}" -f `
            $Module, $Phase, $result.status, $result.detail)
    }
    return $result
}

$active = @(Get-CimInstance Win32_Process | Where-Object {
    $_.Name -in @('lake.exe', 'lean.exe', 'leanchecker.exe')
})
if ($active.Count -ne 0) {
    throw 'Serial Lean window is not free for V97 authentication.'
}

Write-Host 'AUTH V97 generator/manifest/generated sources'
& python $generatorPath
if ($LASTEXITCODE -ne 0) {
    throw "V97 generator authentication failed with exit code $LASTEXITCODE"
}

$manifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$modules = @($manifest.compileSequence | ForEach-Object { [string]$_ })
if ([string]$manifest.schema -ne 'z180-k30-projective-profile-audit-v97/v1') {
    throw 'Unexpected V97 manifest schema.'
}
if ($modules.Count -ne 946 -or
    ($modules | Select-Object -Unique).Count -ne 946) {
    throw "Unexpected V97 compile-sequence length: $($modules.Count)"
}
$memberModules = @($modules | Where-Object { $_ -match 'ProjectiveProfileMembersV97' })
$externalModules = @(
    $manifest.serialReplayPlan.externalAlgebraicModules |
        ForEach-Object { [string]$_ }
)
$externalBuildOnlyModules = @(
    $manifest.serialReplayPlan.buildOnlyExternalAlgebraicModules |
        ForEach-Object { [string]$_ }
)
$externalCheckerModules = @(
    $manifest.serialReplayPlan.checkerExternalAlgebraicModules |
        ForEach-Object { [string]$_ }
)
$handwrittenModules = @(
    $manifest.serialReplayPlan.handwrittenModules |
        ForEach-Object { [string]$_ }
)
$completenessBaseModules = @(
    $manifest.serialReplayPlan.checkerCompletenessBaseModules |
        ForEach-Object { [string]$_ }
)
$dataModules = @(
    $manifest.serialReplayPlan.checkerDataModules |
        ForEach-Object { [string]$_ }
)
$divisorModules = @(
    $manifest.serialReplayPlan.checkerDivisorModules |
        ForEach-Object { [string]$_ }
)
$finalModules = @(
    $manifest.serialReplayPlan.checkerFinalModules |
        ForEach-Object { [string]$_ }
)
$checkerModules = @(
    $manifest.serialReplayPlan.checkerModules |
        ForEach-Object { [string]$_ }
)
$cellModules = @($modules | Where-Object { $_ -match 'ProjectiveProfileCellsV97' })
if ($handwrittenModules.Count -ne 5 -or
    $memberModules.Count -ne 152 -or
    $completenessBaseModules.Count -ne 6 -or
    $externalModules.Count -ne 757 -or
    $externalBuildOnlyModules.Count -ne 751 -or
    $externalCheckerModules.Count -ne 6 -or
    $dataModules.Count -ne 3 -or
    $divisorModules.Count -ne 3 -or
    $finalModules.Count -ne 1 -or
    $checkerModules.Count -ne 24 -or
    $cellModules.Count -ne 19) {
    throw ("Unexpected module partition: handwritten={0}, members={1}, bases={2}, external={3}, externalBuildOnly={4}, externalChecker={5}, cells={6}" -f `
        $handwrittenModules.Count, $memberModules.Count,
        $completenessBaseModules.Count, $externalModules.Count,
        $externalBuildOnlyModules.Count, $externalCheckerModules.Count,
        $cellModules.Count)
}
if (($modules -join "`n") -ne
        (@($manifest.serialReplayPlan.orderedModules) -join "`n") -or
    ($externalModules | Select-Object -Unique).Count -ne 757 -or
    ($externalBuildOnlyModules | Select-Object -Unique).Count -ne 751 -or
    ($externalCheckerModules | Select-Object -Unique).Count -ne 6 -or
    ($checkerModules | Select-Object -Unique).Count -ne 24 -or
    @(Compare-Object $externalModules (
        @($externalBuildOnlyModules + $externalCheckerModules)
    )).Count -ne 0 -or
    @(Compare-Object $checkerModules (
        @($handwrittenModules + $completenessBaseModules +
          $externalCheckerModules + $dataModules + $divisorModules +
          $finalModules)
    )).Count -ne 0 -or
    @(Compare-Object $modules (
        @($handwrittenModules + $memberModules +
          $completenessBaseModules + $externalModules + $dataModules +
          $cellModules + $divisorModules + $finalModules)
    )).Count -ne 0) {
    throw 'Unexpected V97 replay-plan partition.'
}
if ([int]$manifest.totals.uniquePairsRepresented -ne 16796 -or
    [int]$manifest.totals.profileCells -ne 213 -or
    [int]$manifest.totals.exactV87Pointers -ne 222) {
    throw 'Unexpected authenticated V97 census.'
}

$manifestSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $manifestPath).Hash.ToLowerInvariant()
$completed = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
$records = [System.Collections.ArrayList]::new()
$startedAtUtc = [DateTime]::UtcNow.ToString('o')
if (Test-Path -LiteralPath $statePath -PathType Leaf) {
    $oldState = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
    $oldCompletedModules = @(
        $oldState.completedModules | ForEach-Object { [string]$_ }
    )
    $oldCompletedSet = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::Ordinal
    )
    foreach ($module in $oldCompletedModules) {
        [void]$oldCompletedSet.Add($module)
    }
    $reusablePrefix = @(
        @($manifest.serialReplayPlan.handwrittenModules | Where-Object {
            [string]$_ -ne
              'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97'
        }) +
        $manifest.serialReplayPlan.buildOnlyMemberModules |
            ForEach-Object { [string]$_ }
    )
    $prefixSetsMatch = (
        (($oldCompletedModules | Sort-Object) -join "`n") -eq
        (($reusablePrefix | Sort-Object) -join "`n")
    )
    $prefixArtifactsMatch = $true
    foreach ($module in $reusablePrefix) {
        $moduleRelative = ([string]$module).Replace('.', '/')
        $sourceRelative = "fuglede_lean/$moduleRelative.lean"
        $sourcePath = Join-Path $workspaceRoot $sourceRelative
        $oleanRelative = ([string]$module).Replace('.', '\') + '.olean'
        $oleanPath = Join-Path $workspaceRoot `
            (Join-Path 'fuglede_lean\.lake\build\lib\lean' $oleanRelative)
        $expectedProperty = $manifest.generatedFilesSha256.PSObject.Properties[
            $sourceRelative
        ]
        if ($null -eq $expectedProperty) {
            $expectedProperty = $manifest.coreSourcesSha256.PSObject.Properties[
                $sourceRelative
            ]
        }
        if ($null -eq $expectedProperty) {
            $expectedProperty = `
                $manifest.externalAlgebraicSourcesSha256.PSObject.Properties[
                    $sourceRelative
                ]
        }
        if ($null -eq $expectedProperty -or
            -not (Test-Path -LiteralPath $sourcePath -PathType Leaf) -or
            -not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            $prefixArtifactsMatch = $false
            break
        }
        $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
        if ($actualHash -ne [string]$expectedProperty.Value) {
            $prefixArtifactsMatch = $false
            break
        }
    }
    $canMigrateShardedCompleteness = (
        [string]$oldState.manifestSha256 -eq
            '914c3d72461808effc293025c39db1c3177348bcc32e219e71af97d94f31ca6b' -and
        $oldCompletedSet.Count -eq 156 -and
        $prefixSetsMatch -and
        $prefixArtifactsMatch
    )
    $originalPrefixArtifactsMatch = $prefixArtifactsMatch
    $cap16Reusable = $reusablePrefix
    $oldCap20Completed = @(
        $reusablePrefix +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UB00'
    )
    $cap16OldSetMatches = (
        (($oldCompletedModules | Sort-Object) -join "`n") -eq
        (($oldCap20Completed | Sort-Object) -join "`n")
    )
    $cap16ArtifactsMatch = $originalPrefixArtifactsMatch
    foreach ($module in $cap16Reusable) {
        $moduleRelative = ([string]$module).Replace('.', '/')
        $sourceRelative = "fuglede_lean/$moduleRelative.lean"
        $sourcePath = Join-Path $workspaceRoot $sourceRelative
        $oleanRelative = ([string]$module).Replace('.', '\') + '.olean'
        $oleanPath = Join-Path $workspaceRoot `
            (Join-Path 'fuglede_lean\.lake\build\lib\lean' $oleanRelative)
        $expectedProperty = $manifest.generatedFilesSha256.PSObject.Properties[
            $sourceRelative
        ]
        if ($null -eq $expectedProperty) {
            $expectedProperty = $manifest.coreSourcesSha256.PSObject.Properties[
                $sourceRelative
            ]
        }
        if ($null -eq $expectedProperty) {
            $expectedProperty = `
                $manifest.externalAlgebraicSourcesSha256.PSObject.Properties[
                    $sourceRelative
                ]
        }
        if ($null -eq $expectedProperty -or
            -not (Test-Path -LiteralPath $sourcePath -PathType Leaf) -or
            -not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            $cap16ArtifactsMatch = $false
            break
        }
        $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
        if ($actualHash -ne [string]$expectedProperty.Value) {
            $cap16ArtifactsMatch = $false
            break
        }
    }
    $canMigrateCap16Completeness = (
        [string]$oldState.manifestSha256 -eq
            '3666b1f8b21e3595f93969481f1fd4260ad2c0dec35fd0397b3fae089f13ed21' -and
        $oldCompletedSet.Count -eq 163 -and
        $cap16OldSetMatches -and
        $cap16ArtifactsMatch
    )
    $partitionCoreModule =
      'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97'
    $cap10Reusable = @($reusablePrefix + $partitionCoreModule)
    $oldCap16Completed = @(
        $cap10Reusable +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6UBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VBase' +
        'Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UB00'
    )
    $cap10OldSetMatches = (
        (($oldCompletedModules | Sort-Object) -join "`n") -eq
        (($oldCap16Completed | Sort-Object) -join "`n")
    )
    $cap10ArtifactsMatch = $originalPrefixArtifactsMatch
    foreach ($module in $cap10Reusable) {
        $moduleRelative = ([string]$module).Replace('.', '/')
        $sourceRelative = "fuglede_lean/$moduleRelative.lean"
        $sourcePath = Join-Path $workspaceRoot $sourceRelative
        $oleanRelative = ([string]$module).Replace('.', '\') + '.olean'
        $oleanPath = Join-Path $workspaceRoot `
            (Join-Path 'fuglede_lean\.lake\build\lib\lean' $oleanRelative)
        $expectedProperty = $manifest.generatedFilesSha256.PSObject.Properties[
            $sourceRelative
        ]
        if ($null -eq $expectedProperty) {
            $expectedProperty = $manifest.coreSourcesSha256.PSObject.Properties[
                $sourceRelative
            ]
        }
        if ($null -eq $expectedProperty) {
            $expectedProperty = `
                $manifest.externalAlgebraicSourcesSha256.PSObject.Properties[
                    $sourceRelative
                ]
        }
        if ($null -eq $expectedProperty -or
            -not (Test-Path -LiteralPath $sourcePath -PathType Leaf) -or
            -not (Test-Path -LiteralPath $oleanPath -PathType Leaf)) {
            $cap10ArtifactsMatch = $false
            break
        }
        $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
        if ($actualHash -ne [string]$expectedProperty.Value) {
            $cap10ArtifactsMatch = $false
            break
        }
    }
    $canMigrateCap10Completeness = (
        [string]$oldState.manifestSha256 -eq
            'd3dc4d152699de2d447da64a9c121aba5b4dd5ff7ea845fc55e482660f4747f7' -and
        $oldCompletedSet.Count -eq 164 -and
        $cap10OldSetMatches -and
        $cap10ArtifactsMatch
    )
    if ([string]$oldState.manifestSha256 -ne $manifestSha -and
        -not $canMigrateShardedCompleteness -and
        -not $canMigrateCap16Completeness -and
        -not $canMigrateCap10Completeness) {
        throw 'FAIL CLOSED: persisted V97 state belongs to another manifest.'
    }
    $modulesToReuse = if ($canMigrateCap10Completeness) {
        $cap10Reusable
    }
    elseif ($canMigrateCap16Completeness) {
        $cap16Reusable
    }
    else {
        $oldCompletedModules
    }
    foreach ($module in $modulesToReuse) {
        [void]$completed.Add([string]$module)
    }
    foreach ($record in @($oldState.records)) {
        [void]$records.Add($record)
    }
    $startedAtUtc = [string]$oldState.startedAtUtc
    if ($canMigrateShardedCompleteness -or
        $canMigrateCap16Completeness -or
        $canMigrateCap10Completeness) {
        Write-Host ("MIGRATE authenticated modules={0} to current completeness manifest" -f `
            $completed.Count)
        Save-State -ManifestSha $manifestSha -Completed $completed `
            -Records $records -StartedAtUtc $startedAtUtc
    }
    Write-Host ("RESUME completed={0}" -f $completed.Count)
}

$buildOnly = [System.Collections.Generic.HashSet[string]]::new(
    [System.StringComparer]::Ordinal
)
foreach ($module in @(
    $memberModules + $externalBuildOnlyModules + $cellModules
)) {
    [void]$buildOnly.Add([string]$module)
}

Write-Host ("PLAN modules={0} buildOnly={1} checker={2} capBytes={3}" -f `
    $modules.Count, $buildOnly.Count, ($modules.Count - $buildOnly.Count), $capBytes)
$ordinal = 0
foreach ($module in $modules) {
    $ordinal += 1
    if ($completed.Contains($module)) {
        Write-Host ("SKIP [{0}/{1}] {2}" -f $ordinal, $modules.Count, $module)
        continue
    }
    Write-Host ("MODULE [{0}/{1}] {2}" -f $ordinal, $modules.Count, $module)
    try {
        $build = Invoke-IsolatedPhase -Module $module -Phase build
        $checker = $null
        if (-not $buildOnly.Contains($module)) {
            $checker = Invoke-IsolatedPhase -Module $module -Phase checker
        }
    }
    catch {
        [void]$records.Add([pscustomobject]@{
            module = $module
            phase = 'failed'
            status = 'failed'
            atUtc = [DateTime]::UtcNow.ToString('o')
            detail = $_.Exception.Message
        })
        Save-State -ManifestSha $manifestSha -Completed $completed `
            -Records $records -StartedAtUtc $startedAtUtc
        throw
    }
    [void]$completed.Add($module)
    [void]$records.Add([pscustomobject]@{
        module = $module
        phase = 'sealed'
        status = 'passed'
        atUtc = [DateTime]::UtcNow.ToString('o')
        buildMaxLeanWorkingSetBytes = [uint64]$build.maxLeanWorkingSetBytes
        checkerPolicy = if ($null -eq $checker) { 'transitive-root' } else { 'individual' }
        checkerMaxLeanWorkingSetBytes = if ($null -eq $checker) { $null } else {
            [uint64]$checker.maxLeanWorkingSetBytes
        }
    })
    Save-State -ManifestSha $manifestSha -Completed $completed `
        -Records $records -StartedAtUtc $startedAtUtc
    Write-Host ("SEALED [{0}/{1}] {2}" -f $ordinal, $modules.Count, $module)
    if (Test-Path -LiteralPath $pausePath -PathType Leaf) {
        Remove-Item -LiteralPath $pausePath -Force
        Write-Host ("PAUSED clean-boundary completed={0}" -f $completed.Count)
        exit 0
    }
}

Write-Host ("COMPLETE modules={0} manifestSha256={1}" -f `
    $completed.Count, $manifestSha)
