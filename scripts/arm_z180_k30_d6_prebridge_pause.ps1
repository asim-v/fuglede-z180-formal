[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [uint32]$DriverPid
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$workspaceRoot = Split-Path -Parent $scriptRoot
$auditRoot = Join-Path $workspaceRoot `
    'audit\z180_k30_projective_d6_algebraic_v97'
$statePath = Join-Path $auditRoot 'state.json'
$pausePath = Join-Path $auditRoot 'pause.request'
$statusPath = Join-Path $auditRoot 'prebridge-pause-watcher.json'
$lockPath = Join-Path $auditRoot 'prebridge-pause-watcher.lock'
$targetModule =
    'Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicLeaf314PilotV97'

try {
    $lockStream = [System.IO.File]::Open(
        $lockPath,
        [System.IO.FileMode]::OpenOrCreate,
        [System.IO.FileAccess]::ReadWrite,
        [System.IO.FileShare]::None
    )
} catch [System.IO.IOException] {
    # Another authenticated watcher owns the unique boundary monitor.
    exit 0
}

try {
    if (Test-Path -LiteralPath $pausePath -PathType Leaf) {
        throw 'Refusing to arm over a stale D6 pause request.'
    }
    $driver = Get-CimInstance Win32_Process -Filter "ProcessId = $DriverPid"
    if ($null -eq $driver -or $driver.Name -ne 'powershell.exe' -or
        $null -eq $driver.CommandLine -or
        -not $driver.CommandLine.Contains('run_z180_k30_d6_algebraic_v97.ps1')) {
        throw "PID $DriverPid is not the authenticated D6 serial driver."
    }

    while ($true) {
        $pollMilliseconds = 5000
        $liveDriver = Get-CimInstance Win32_Process `
            -Filter "ProcessId = $DriverPid"
        if ($null -eq $liveDriver -or $liveDriver.Name -ne 'powershell.exe' -or
            $null -eq $liveDriver.CommandLine -or
            -not $liveDriver.CommandLine.Contains(
                'run_z180_k30_d6_algebraic_v97.ps1'
            )) {
            throw "Authenticated D6 driver PID $DriverPid exited or changed."
        }
        if (Test-Path -LiteralPath $statePath -PathType Leaf) {
            $state = Get-Content -Raw -LiteralPath $statePath | ConvertFrom-Json
            $completed = @($state.completedModules).Count
            if ($completed -gt 573) {
                throw "Pre-Bridge pause boundary was missed: completed=$completed"
            }
            if ($completed -eq 573) {
                if (-not (Test-Path -LiteralPath $pausePath -PathType Leaf)) {
                    throw 'Leaf314 completed before the authenticated pause was armed.'
                }
                break
            }
            if ($completed -eq 572) {
                $pollMilliseconds = 200
                $targetActive = @(Get-CimInstance Win32_Process | Where-Object {
                    $_.ParentProcessId -eq $DriverPid -and
                    $_.Name -eq 'powershell.exe' -and
                    $null -ne $_.CommandLine -and
                    $_.CommandLine.Contains(
                        'run_z180_k30_projective_cap20_pilot_v89.ps1'
                    ) -and
                    $_.CommandLine.Contains("-Module $targetModule") -and
                    $_.CommandLine.Contains('-Phase build')
                })
                if ($targetActive.Count -eq 1) {
                    New-Item -ItemType File -Path $pausePath -Force | Out-Null
                    break
                }
                if ($targetActive.Count -gt 1) {
                    throw 'Multiple owned Leaf314 phase runners are active.'
                }
            }
            if ($completed -ge 570) {
                $pollMilliseconds = 200
            }
        }
        Start-Sleep -Milliseconds $pollMilliseconds
    }

    [ordered]@{
        schema = 'z180-k30-d6-prebridge-pause-watcher-v2'
        armedAtUtc = [DateTime]::UtcNow.ToString('o')
        driverPid = $DriverPid
        targetModule = $targetModule
        pauseRequest = $pausePath
    } | ConvertTo-Json -Depth 4 |
        Set-Content -LiteralPath $statusPath -Encoding UTF8
} finally {
    $lockStream.Dispose()
}
