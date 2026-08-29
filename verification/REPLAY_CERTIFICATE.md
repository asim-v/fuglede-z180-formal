# Release replay certificate

| Field | Value |
| --- | --- |
| Release | `v2.0.0` |
| Date | 2026-08-28 |
| Scope | Fuglede's conjecture for `ZMod 180` |
| Public theorem | `Fuglede.z180_tiles_iff_spectral` |
| Status | **PASS** |

The public theorem proves, for every `A : Finset (ZMod 180)`, the
biconditional

```lean
(∃ B : Finset (ZMod 180), Tiles A B) ↔
  ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L
```

## Release snapshot

| Item | Value |
| --- | --- |
| Lean modules | 2,411 |
| Lean source bytes | 25,405,989 |
| Lean source lines | 294,748 |
| Authenticated inputs | 2,415 |
| Lean | `v4.31.0` |
| mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Release-manifest SHA-256 | `1A84333792D22292918C2814EE8657D68191F4C5C7E8FE50767205C1B3FDFF36` |
| PDF size | 561,709 bytes |
| PDF SHA-256 | `6C4FE1F0A65127C7FEBAFC5C3CC4189696C695C36E0603C687F2231E7C3EDD40` |

## Endpoint replay

| Module | Role | Source SHA-256 | Checked `.olean` SHA-256 |
| --- | --- | --- | --- |
| `Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97` | Exceptional `\|A\| = 30` projective-profile aggregate | `83C54B8D6BBCE9504EE4AA977BC9B9B421B9348D842D97C28A0FC8C39E962D7C` | `0165B255F75535C004536091E562BB521DCA78A263A5D7AFE63D97E3DE18EE94` |
| `Fuglede.Z180K30CatalogueMasterClosureV81` | Master catalogue assembly | `50F50D7D002931FE343D92A8DD7438964A352FE0A8F9EEBF09FF6C067195C428` | `95A506F5B6AD131672C4AF8A578554EB0494BE1A24890FEEF9D16BEC1EA42B11` |
| `Fuglede.Z180K30UnconditionalCatalogueClosureV96` | Spectral implies tiling endpoint | `B69FC2F206015BDA5B72172F2CD6F34EFE799BEA8DC73FE573F1D9725F3E49A3` | `A34B0DB199D7B3F314F359A836D90B907E73CAC832E21BC69B2847416E3B4218` |
| `Fuglede.Z180TilingSpectralClosureV12` | Tiling implies spectral endpoint | `EE8BDB1FA61CD0A835B1B4DA209470359ED40370A2D56678AB2101BCBCA931EC` | `1EC068BFF7E768948CD49821EA7A2957414E302CA42036FD6F2C0C41B40A7A4B` |
| `Fuglede.Z180FugledeTheorem` | Public biconditional theorem | `F947D09E39B23FF24D012C403F19C2AD3AB50A9263E11459CC330016DFE85A51` | `54B7A3C356B188DB0C9A84953B24A3DED0D4138BC7A2B35DC5569CFDF243D063` |

The serialized release commands are:

```powershell
Set-Location fuglede_lean
$env:LAKE_JOBS = "1"

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

A Windows short-path mirror is used to avoid `MAX_PATH`; its source inputs must
be byte-identical to the authenticated release snapshot.

The replay completed with the following results:

1. the build completed 2,411/2,411 modules;
2. all five `leanchecker` invocations exited with code 0;
3. every checked wrapper's `#print axioms` report was exactly
   `[propext, Classical.choice, Quot.sound]`;
4. all five checked-object hashes were recorded above.

## Provenance and trust

The V97 provenance hashes are:

- manifest:
  `8F88C66CC06CC0D467C892891059C26ED287501EC530169257C06BE854C6AEB8`;
- generator:
  `874D3CE14EF3739C33273E91338D040238550EA02DB180E903A7DD329FBD413D`;
- sealed state:
  `73DB6E1C654A221B68CA0FC8592410787B9DB48163B3C5643039EC8FD8FE350B`.

The logical trust boundary is the Lean kernel, pinned mathlib sources, and the
standard axioms printed above. Python, PowerShell, JSON manifests,
orchestration code, and the PDF are not trusted proof components.

The five-page PDF passed visual, font, reference, citation, overflow, and
encoding checks. Detailed reproduction and QA information is in
[`README.md`](README.md).
