# Proof map

This page traces the final biconditional from its mathematical statement to
the Lean modules that establish it. Every link below belongs to the exact
transitive import closure of `Fuglede/Z180FugledeTheorem.lean`.

## Final endpoint

[`Fuglede/Z180FugledeTheorem.lean`](../fuglede_lean/Fuglede/Z180FugledeTheorem.lean)
proves:

```lean
theorem z180_tiles_iff_spectral (A : Finset (ZMod 180)) :
    (∃ B : Finset (ZMod 180), Tiles A B) ↔
      ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L
```

It combines two independently checked endpoints:

- `z180_exists_tiling_of_spectral_v96`;
- `z180_exists_spectrum_of_tile_v12`.

## Exact finite statement

- [`CyclicCertificate.lean`](../fuglede_lean/Fuglede/CyclicCertificate.lean)
  defines the integer mask polynomial, `CyclotomicZero`, and
  `CyclotomicSpectrum`.
- [`SpectralFourier.lean`](../fuglede_lean/Fuglede/SpectralFourier.lean)
  identifies cyclotomic divisibility with exact Fourier vanishing and proves
  that `CyclotomicSpectrum` is the usual finite Fourier spectrum condition.
- [`FiniteTiling.lean`](../fuglede_lean/Fuglede/FiniteTiling.lean) defines
  `Tiles A B` as bijectivity of the addition map.
- [`FourierTiling.lean`](../fuglede_lean/Fuglede/FourierTiling.lean) proves the
  exact Fourier and cyclotomic zero-cover characterization of a tiling pair.

## Spectral implies tiling

### Global reduction

- [`Z180CardinalitySieve.lean`](../fuglede_lean/Fuglede/Z180CardinalitySieve.lean)
  restricts lower-half spectral cardinalities to divisors of `180` or the
  exceptional list `7, 8, 11, 13, 14, 16, 17, 19, 21, 24, 27, 33`.
- [`Z180MasterReduction.lean`](../fuglede_lean/Fuglede/Z180MasterReduction.lean)
  combines the upper-half theorem, divisor reduction, and nondivisor
  exclusions.
- [`Z180MasterConditionalClosure.lean`](../fuglede_lean/Fuglede/Z180MasterConditionalClosure.lean)
  joins the completed cardinality branches and leaves only `|A| = 30`.
- [`Z180K30CatalogueMasterClosureV81.lean`](../fuglede_lean/Fuglede/Z180K30CatalogueMasterClosureV81.lean)
  turns a complete exceptional catalogue into the global implication.

### Exceptional cardinality 30

The final finite proof separates marginal information from coupled data.

- [`Z180K30ExceptionalProjectiveHistogramCoreV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveHistogramCoreV97.lean)
  proves the ordered-difference bilinear identity and symmetry.
- [`Z180K30ExceptionalProjectiveProfileCoreV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveProfileCoreV97.lean)
  proves that the profile dot product is the scalar Gram coefficient.
- Generated V97 member, data, cell, and divisor modules certify all 213
  profile cells and 222 positive witness pointers.
- [`Z180K30ExceptionalProjectiveProfileAggregateV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveProfileAggregateV97.lean)
  exposes the completed projective normalization.
- [`Z180K30ExceptionalCommonFrameCovarianceV93.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalCommonFrameCovarianceV93.lean)
  transports all five Gram coordinates through one affine frame.
- [`Z180K30ExceptionalFramedCandidateExtractionV95.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalFramedCandidateExtractionV95.lean)
  constructs the coupled framed-star witness.
- [`Z180K30UnconditionalCatalogueClosureV96.lean`](../fuglede_lean/Fuglede/Z180K30UnconditionalCatalogueClosureV96.lean)
  joins V97, V95, and V81 and proves the implication for every subset.

### Authenticated finite census

| Divisor | U profiles | V profiles | Profile cells | Positive pairs |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 5 | 35 | 175 | 42 |
| 4 | 4 | 7 | 28 | 0 |
| 6 | 10 | 1 | 10 | 180 |
| **Total** | **19** | **43** | **213** | **222** |

The literal universe has 16,796 pairs. Exactly 16,574 are refuted by an exact
integer coefficient; the remaining 222 point to explicit catalogue witnesses.

## Tiling implies spectral

### Zero cover and cardinality reduction

[`FourierTiling.lean`](../fuglede_lean/Fuglede/FourierTiling.lean) proves that a
tiling pair has the correct cardinality product and covers every nonzero
frequency by a Fourier zero of one factor. It also proves the converse by
Fourier inversion.

[`Z180TilingSpectralReduction.lean`](../fuglede_lean/Fuglede/Z180TilingSpectralReduction.lean)
starts the endpoint cases. The modules
`Z180TilingSpectralReductionV2` through `V11` close the eighteen divisors of
`180` in stages. They use:

- direct one-, two-, and three-point character constructions;
- prime-power allocation for sizes `4`, `5`, and `9`;
- small-complement constructions for sizes `60` and `90`;
- exact forcing at sizes `20`, `36`, and `45`;
- quotient descent for sizes `10`, `12`, `15`, and `18`.

### The six-point core

[`Z36Card6TilingToSpectral.lean`](../fuglede_lean/Fuglede/Z36Card6TilingToSpectral.lean)
proves that every six-point tile of `ZMod 36` is spectral. The zero cover
allocates one of orders `2,4` and one of orders `3,9` to each factor. Checked
forcing lemmas reduce the result to five explicit spectrum patterns.

The same module proves the six-point case in `ZMod 180` by injective descent
modulo `36` and lifting frequencies by multiplication by five.

### The thirty-point case

[`Z180TilingCard30Descent.lean`](../fuglede_lean/Fuglede/Z180TilingCard30Descent.lean)
handles a thirty-point tile `A` and its six-point complement `B`:

1. dilate `B` by five and retain a tiling pair;
2. project `B` injectively to a six-point set in `ZMod 36`;
3. choose a checked six-frequency set with nonzero complementary transform;
4. lift all five fibres to obtain a 30-point spectrum for `A`.

[`Z180TilingSpectralClosureV12.lean`](../fuglede_lean/Fuglede/Z180TilingSpectralClosureV12.lean)
joins this case to the V11 cardinality reduction and proves tiling-to-spectral
for every subset of `ZMod 180`.

## Kernel boundary

The final closure contains no `sorry`, `admit`, project-defined axiom,
`unsafe`, or `native_decide`. Python and PowerShell files document generation
and provenance, but the final theorem trusts only Lean's kernel, the pinned
mathlib sources, and the standard axioms printed by `#print axioms`.
