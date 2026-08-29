# Verification record

## Scope and release status

Release `v2.0.0`, dated 2026-08-28, formalizes both directions of
Fuglede's conjecture for the single finite cyclic group `ZMod 180`.

The public theorem is
`Fuglede.z180_tiles_iff_spectral` in
`fuglede_lean/Fuglede/Z180FugledeTheorem.lean`:

```lean
theorem z180_tiles_iff_spectral (A : Finset (ZMod 180)) :
    (∃ B : Finset (ZMod 180), Tiles A B) ↔
      ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L
```

No statement about another cyclic group or a general Fuglede theorem is part of
this release. The final serialized replay completed successfully: the build
reached 2,411/2,411, all five `leanchecker` commands exited with code 0, and
every wrapper's `#print axioms` report was exactly
`[propext, Classical.choice, Quot.sound]`.

## Authenticated release snapshot

The exact transitive local source closure contains:

- 2,411 Lean modules;
- 25,405,989 Lean source bytes;
- 294,748 Lean source lines;
- 2,415 authenticated release inputs;
- zero missing local imports.

The machine-readable source of truth is
[`Z180_RELEASE_SHA256.txt`](Z180_RELEASE_SHA256.txt).

| Artifact | SHA-256 |
| --- | --- |
| `verification/Z180_RELEASE_SHA256.txt` | `1A84333792D22292918C2814EE8657D68191F4C5C7E8FE50767205C1B3FDFF36` |
| `fuglede_lean/lean-toolchain` | `1550DC85BB00026CC586C6390F0AF6D6B84C0AEF210F4B8B44EFDC6812EF6256` |
| `fuglede_lean/lake-manifest.json` | `F1B27D13D436934209CF3ECF04835EF2436D60EADBEB4E493A8093EAB1F18D00` |
| `paper/main.pdf` | `6C4FE1F0A65127C7FEBAFC5C3CC4189696C695C36E0603C687F2231E7C3EDD40` |

Toolchain:

- Lean `v4.31.0`;
- mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

## Endpoint roles and hashes

| Module | Role | Source SHA-256 | Checked `.olean` SHA-256 |
| --- | --- | --- | --- |
| `Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97` | Exceptional `\|A\| = 30` projective-profile aggregate | `83C54B8D6BBCE9504EE4AA977BC9B9B421B9348D842D97C28A0FC8C39E962D7C` | `0165B255F75535C004536091E562BB521DCA78A263A5D7AFE63D97E3DE18EE94` |
| `Fuglede.Z180K30CatalogueMasterClosureV81` | Master catalogue assembly | `50F50D7D002931FE343D92A8DD7438964A352FE0A8F9EEBF09FF6C067195C428` | `95A506F5B6AD131672C4AF8A578554EB0494BE1A24890FEEF9D16BEC1EA42B11` |
| `Fuglede.Z180K30UnconditionalCatalogueClosureV96` | Spectral implies tiling endpoint | `B69FC2F206015BDA5B72172F2CD6F34EFE799BEA8DC73FE573F1D9725F3E49A3` | `A34B0DB199D7B3F314F359A836D90B907E73CAC832E21BC69B2847416E3B4218` |
| `Fuglede.Z180TilingSpectralClosureV12` | Tiling implies spectral endpoint | `EE8BDB1FA61CD0A835B1B4DA209470359ED40370A2D56678AB2101BCBCA931EC` | `1EC068BFF7E768948CD49821EA7A2957414E302CA42036FD6F2C0C41B40A7A4B` |
| `Fuglede.Z180FugledeTheorem` | Public biconditional theorem | `F947D09E39B23FF24D012C403F19C2AD3AB50A9263E11459CC330016DFE85A51` | `54B7A3C356B188DB0C9A84953B24A3DED0D4138BC7A2B35DC5569CFDF243D063` |

All five checked objects were produced by the release replay below.

## Serialized Windows replay

Windows validation uses a byte-identical short-path mirror because the original
workspace path can exceed `MAX_PATH`. This is only a filesystem workaround; the
mirror sources must authenticate against `Z180_RELEASE_SHA256.txt`.

For a clean public replay, clone directly to a short path and serialize Lake to
limit peak memory:

```powershell
git clone --branch v2.0.0 https://github.com/asim-v/fuglede-z180-formal.git C:\tmp\z180-v2
Set-Location C:\tmp\z180-v2\fuglede_lean
$env:LAKE_JOBS = "1"

lake update
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake exe cache get
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

lake build '+Fuglede.Z180FugledeTheorem:olean'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

$modules = @(
  "Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97",
  "Fuglede.Z180K30CatalogueMasterClosureV81",
  "Fuglede.Z180K30UnconditionalCatalogueClosureV96",
  "Fuglede.Z180TilingSpectralClosureV12",
  "Fuglede.Z180FugledeTheorem"
)

foreach ($module in $modules) {
  lake env leanchecker -v $module
  if ($LASTEXITCODE -ne 0) {
    throw "leanchecker failed for $module"
  }
}
```

Extract the object hashes after the build with:

```powershell
foreach ($module in $modules) {
  $relative = $module.Replace(".", "\") + ".olean"
  $path = Join-Path ".lake\build\lib\lean" $relative
  Get-FileHash -Algorithm SHA256 $path
}
```

In the release replay, every checked wrapper's `#print axioms` command reported
exactly the standard axiom set:

```text
[propext, Classical.choice, Quot.sound]
```

All five `leanchecker` invocations exited with code 0. No problem-specific axiom
was reported.

## Source and V97 provenance

From the repository root:

```powershell
python scripts\audit_z180_release.py
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }

python scripts\generate_z180_k30_projective_profile_audit_v97.py
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
```

The first command authenticates the complete 2,415-input release snapshot. The
second checks the deterministic V97 profile DAG and its witness pointers.

| V97 provenance artifact | Role | SHA-256 |
| --- | --- | --- |
| `scripts/z180_k30_projective_profile_audit_v97.manifest.json` | Authenticated V97 replay plan | `8F88C66CC06CC0D467C892891059C26ED287501EC530169257C06BE854C6AEB8` |
| `scripts/generate_z180_k30_projective_profile_audit_v97.py` | Deterministic generator and checker | `874D3CE14EF3739C33273E91338D040238550EA02DB180E903A7DD329FBD413D` |
| `audit/z180_k30_projective_d6_u_validity_v97/state.json` | Sealed D6 validity state | `73DB6E1C654A221B68CA0FC8592410787B9DB48163B3C5643039EC8FD8FE350B` |

The authenticated V97 plan contains 946 unique modules: 922 build-only modules
and 24 checker roots. Its finite census contains 16,796 literal pairs, 213
profile cells, 222 witness pointers, and 184 generated Lean files.

## Trust boundary

The logical result depends on the Lean 4 kernel, the pinned mathlib sources, and
the three standard principles reported above. Python and PowerShell scripts,
JSON manifests, orchestration logic, and the article PDF are not part of the
logical trust base. They generate, authenticate, or present inputs whose final
declarations are elaborated by Lean and replayed by `leanchecker`.

The proof path uses exact finite data, integer polynomials, finite lists, and
kernel-reduced decisions. It does not rely on floating-point arithmetic.

## PDF quality assurance

`paper/main.pdf` passed the release layout audit:

- 5 pages and 561,709 bytes;
- all fonts embedded;
- zero overfull boxes;
- zero undefined references or citations;
- zero rerun requests;
- five harmless underfull-box notices;
- no detected mojibake;
- visual review of all pages, including the replay block on page 5, passed.

Rebuild it from the repository root with:

```powershell
powershell -ExecutionPolicy Bypass -File paper\build.ps1
```
