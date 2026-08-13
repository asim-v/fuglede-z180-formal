$ErrorActionPreference = 'Stop'
$paperRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Push-Location $paperRoot
try {
    tectonic main.tex --keep-logs
    if ($LASTEXITCODE -ne 0) {
        throw "Tectonic failed with exit code $LASTEXITCODE"
    }
}
finally {
    Pop-Location
}

