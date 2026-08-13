# Proof map

This page gives a short route from the mathematical statement to the Lean
files that establish it.

## Exact finite statement

- [`Fuglede/CyclicCertificate.lean`](../fuglede_lean/Fuglede/CyclicCertificate.lean)
  defines the mask polynomial, cyclotomic Fourier-zero certificate, and
  `CyclotomicSpectrum`.
- [`Fuglede/FiniteTiling.lean`](../fuglede_lean/Fuglede/FiniteTiling.lean) defines
  `Tiles A B` as bijectivity of the addition map.

## Global reduction

- [`Fuglede/Z180MasterConditionalClosure.lean`](../fuglede_lean/Fuglede/Z180MasterConditionalClosure.lean)
  combines the completed cardinality branches and isolates the exceptional
  `|A| = 30` closure.
- [`Fuglede/Z180K30CatalogueMasterClosureV81.lean`](../fuglede_lean/Fuglede/Z180K30CatalogueMasterClosureV81.lean)
  converts a complete exceptional catalogue into the global theorem.

## Exceptional K30 branch

The K30 proof separates two forms of finite information.

### Marginal/projective branch (V97)

- [`Z180K30ExceptionalProjectiveHistogramCoreV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveHistogramCoreV97.lean)
  proves the ordered-difference bilinear formula and its symmetry.
- [`Z180K30ExceptionalProjectiveProfileCoreV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveProfileCoreV97.lean)
  proves that a projective profile dot product equals the scalar Gram
  coefficient.
- The generated `Members`, `Data`, `Cells`, and `Divisor` modules certify the
  213 profile cells and 222 exact catalogue pointers.
- [`Z180K30ExceptionalProjectiveProfileAggregateV97.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalProjectiveProfileAggregateV97.lean)
  exposes `z180_k30_projective_normalization_v97`.

### Coupled/common-frame branch (V95)

- [`Z180K30ExceptionalCommonFrameCovarianceV93.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalCommonFrameCovarianceV93.lean)
  transports the five Gram coordinates through one common affine frame.
- [`Z180K30ExceptionalFramedCandidateExtractionV95.lean`](../fuglede_lean/Fuglede/Z180K30ExceptionalFramedCandidateExtractionV95.lean)
  combines trace classification, affine candidates, and exact signatures to
  build the framed-star catalogue.

## Final assembly

- [`Z180K30UnconditionalCatalogueClosureV96.lean`](../fuglede_lean/Fuglede/Z180K30UnconditionalCatalogueClosureV96.lean)
  joins V97, V95, and V81. Its final theorem is:

```lean
theorem z180_exists_tiling_of_spectral_v96
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B
```

## Finite census

| Divisor | U profiles | V profiles | Profile cells | Positive pairs |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 5 | 35 | 175 | 42 |
| 4 | 4 | 7 | 28 | 0 |
| 6 | 10 | 1 | 10 | 180 |
| **Total** | **19** | **43** | **213** | **222** |

The literal universe contains 16,796 distinct pairs. Exactly 16,574 are
refuted at the scalar coefficient and the remaining 222 are linked to explicit
catalogue witnesses.
