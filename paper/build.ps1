$ErrorActionPreference = 'Stop'
$paperRoot = Split-Path -Parent $MyInvocation.MyCommand.Path

function Invoke-TeXStep {
    param(
        [Parameter(Mandatory = $true)][string]$Program,
        [Parameter(Mandatory = $true)][string[]]$Arguments
    )

    & $Program @Arguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Program failed with exit code $LASTEXITCODE"
    }
}

Push-Location $paperRoot
try {
    $pdfArgs = @('-interaction=nonstopmode', '-halt-on-error', 'main.tex')
    Invoke-TeXStep -Program 'pdflatex' -Arguments $pdfArgs
    Invoke-TeXStep -Program 'bibtex' -Arguments @('main')
    Invoke-TeXStep -Program 'pdflatex' -Arguments $pdfArgs
    Invoke-TeXStep -Program 'pdflatex' -Arguments $pdfArgs

    Write-Host "Built $paperRoot\main.pdf"
}
finally {
    Pop-Location
}
