param()

$ErrorActionPreference = 'Stop'
$workspace = Split-Path -Parent $PSCommandPath
$manifestPath = Join-Path $workspace 'Fuglede\Z180K30ExceptionalFramedCandidateExtractionV95.manifest.json'
$manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
$errors = [System.Collections.Generic.List[string]]::new()

if ($manifest.schema -ne 'z180-k30-framed-candidate-source-manifest/v1') {
  $errors.Add("Unexpected manifest schema: $($manifest.schema)")
}
if ($manifest.sources.Count -ne $manifest.expected_source_count) {
  $errors.Add("Manifest count $($manifest.sources.Count) != expected $($manifest.expected_source_count)")
}
$manifestPaths = @($manifest.sources | ForEach-Object path)
$buildOrder = @($manifest.build_order)
if (($buildOrder -join "`n") -cne ($manifestPaths -join "`n")) {
  $errors.Add('Build order is not the exact manifest source order')
}

$expectedLeaves = @($manifest.sources | Where-Object {
  [IO.Path]::GetFileName($_.path) -match '^Z180K30ExceptionalAffineCandidateAuditV95O[024]U(01|05|07|11|13|17|19|23|25|29|31|35)\.lean$'
} | ForEach-Object { [IO.Path]::GetFileName($_.path) } | Sort-Object)
$actualLeaves = @(Get-ChildItem -LiteralPath (Join-Path $workspace 'Fuglede') -Filter 'Z180K30ExceptionalAffineCandidateAuditV95O*.lean' |
  ForEach-Object Name | Sort-Object)
if ($expectedLeaves.Count -ne 36) {
  $errors.Add("Manifest leaf count $($expectedLeaves.Count) != 36")
}
if (($actualLeaves -join "\n") -cne ($expectedLeaves -join "\n")) {
  $errors.Add('Fixed-unit leaf set differs from manifest (missing or unexpected leaf)')
}

$forbiddenPattern = '(?m)\b(sorry|admit|axiom|native_decide)\b'
foreach ($entry in $manifest.sources) {
  $path = Join-Path $workspace ($entry.path -replace '/', [IO.Path]::DirectorySeparatorChar)
  if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
    $errors.Add("Missing source: $($entry.path)")
    continue
  }
  $actualHash = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($actualHash -cne $entry.sha256) {
    $errors.Add("SHA256 mismatch: $($entry.path)")
  }
  $text = Get-Content -LiteralPath $path -Raw
  if ($text -cmatch $forbiddenPattern) {
    $errors.Add("Forbidden proof token '$($Matches[1])': $($entry.path)")
  }
  $actualImports = @(Select-String -LiteralPath $path -Pattern '^import ' |
    ForEach-Object { $_.Line.Substring(7) })
  $expectedImports = @($entry.imports)
  if ($actualImports.Count -ne $expectedImports.Count) {
    $errors.Add("Import count mismatch: $($entry.path)")
  } else {
    for ($i = 0; $i -lt $actualImports.Count; $i++) {
      if ($actualImports[$i] -cne $expectedImports[$i]) {
        $errors.Add("Import order mismatch at index $($i): $($entry.path)")
        break
      }
    }
  }
}

if ($errors.Count -ne 0) {
  foreach ($message in $errors) { [Console]::Error.WriteLine("FAIL: $message") }
  exit 1
}
Write-Output "PASS: $($manifest.sources.Count) sources, 36 leaves, hashes/import order/tokens verified"
