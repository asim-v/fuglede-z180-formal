# A kernel-checked spectral-to-tiling theorem for `Z/180Z`

This repository contains a Lean 4 formalization of the spectral-to-tiling
direction of Fuglede's conjecture for the cyclic group `ZMod 180`, together
with a two-column article explaining the mathematics and the verification
architecture.

- **Author:** Javier Emilio Bazán Sanchez
- **Affiliation:** Facultad de Ciencias, Universidad Nacional Autónoma de México (UNAM)
- **Contact:** [bazan@ciencias.unam.mx](mailto:bazan@ciencias.unam.mx)

## Main theorem

The public endpoint is
[`Fuglede.z180_exists_tiling_of_spectral_v96`](fuglede_lean/Fuglede/Z180K30UnconditionalCatalogueClosureV96.lean):

```lean
theorem z180_exists_tiling_of_spectral_v96
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B
```

Here `CyclotomicSpectrum` is an exact algebraic encoding of pairwise Fourier
orthogonality by divisibility of the mask polynomial by the appropriate
cyclotomic polynomial. The development proves
[`cyclotomicSpectrum_iff_fourierSpectrum`](fuglede_lean/Fuglede/SpectralFourier.lean),
so this is equivalent to the usual finite Fourier definition rather than a
weaker proxy. `Tiles A B` means that the addition map
`A × B → ZMod 180` is bijective, so every group element has a unique
representation `a + b`.

The checked proof has three final components:

1. **V97 projective-profile audit.** A histogram/profile compression reduces
   16,796 literal pairs to 213 profile cells. The 222 positive pairs are tied
   to exact catalogue locations; all other pairs are refuted by an integer
   scalar coefficient.
2. **V95 common-frame catalogue.** A finite affine/covariance argument
   extracts compatible candidates for the coupled five-Gram configuration.
3. **V81/V96 closure.** The two finite certificates discharge the remaining
   `|A| = 30` catalogue hypothesis and connect it to the global cardinality
   reduction for `ZMod 180`.

The global reduction itself includes the upper-half argument, an exact
cardinality sieve, the divisor cases, the nondivisor exclusions, and the
separate closures at sizes `6`, `10`, `12`, `18`, `24`, and `33`. The K30
catalogue is the final branch, not the whole proof in isolation.

## Repository map

| Path | Purpose |
| --- | --- |
| [`paper/main.tex`](paper/main.tex) | Publication-ready two-column article |
| [`paper/main.pdf`](paper/main.pdf) | Rendered article |
| [`fuglede_lean/`](fuglede_lean/) | Complete pinned Lean project |
| [`fuglede_lean/Fuglede/`](fuglede_lean/Fuglede/) | Lean source tree |
| [`scripts/`](scripts/) | Generators, fail-closed manifests, and replay drivers |
| [`generated/`](generated/) | Child manifests used by the compressed K30 audit |
| [`certificates/`](certificates/) | Small external certificate inputs |
| [`docs/PROOF_MAP.md`](docs/PROOF_MAP.md) | Human-readable map from theorem to implementation |
| [`verification/README.md`](verification/README.md) | Exact verification commands and trust boundary |

## Reproduce

The repository pins Lean `v4.31.0` and mathlib commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

```bash
cd fuglede_lean
lake update
lake build Fuglede.Z180K30UnconditionalCatalogueClosureV96
lake env leanchecker -v Fuglede.Z180K30UnconditionalCatalogueClosureV96
cd ..
```

Authenticate the compressed V97 source DAG and its 946-module replay plan:

```bash
python scripts/generate_z180_k30_projective_profile_audit_v97.py
```

On Windows PowerShell, the serialized replay is:

```powershell
powershell -ExecutionPolicy Bypass `
  -File scripts/run_z180_k30_projective_profile_audit_v97.ps1
```

See [`verification/README.md`](verification/README.md) for the endpoint hashes,
checker policy, and the distinction between source authentication and kernel
replay.

## Verification policy

The release sources contain no `sorry`, project-defined `axiom`,
`native_decide`, or `unsafe` in the authenticated V97 proof DAG. Large finite
checks are split into small ordinary-kernel certificates and composed by proved
lemmas. The final `#print axioms` output lists only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

These are the standard classical/quotient axioms used throughout mathlib.

## Scope

The theorem proves the **spectral-to-tiling** implication for the exact
cyclotomic spectrum predicate on `ZMod 180`. It does not yet claim the full
converse, nor a theorem for arbitrary finite abelian groups or arbitrary
moduli.

Work on the converse is tracked in
[`Z180TilingSpectralReduction.lean`](fuglede_lean/Fuglede/Z180TilingSpectralReduction.lean).
The current kernel-checked foundation proves, for every cyclic modulus, that a
tiling pair is equivalent to the correct cardinality identity together with an
exact Fourier (equivalently cyclotomic) zero cover. At modulus `180` it also
proves that tile cardinalities are positive divisors of `180`, closes the
singleton and full-group spectral endpoints, and lists explicitly the sixteen
remaining cardinalities. These are reductions toward tiling-to-spectrality,
not a claim that the converse has already been completed.

## License and citation

The Lean code and repository documentation are released under the MIT License.
The article may be redistributed with attribution. Citation metadata are in
[`CITATION.cff`](CITATION.cff).
