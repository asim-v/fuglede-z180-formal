# Fuglede's conjecture for `Z/180Z`, checked in Lean 4

This repository contains a kernel-checked proof of the finite cyclic Fuglede
conjecture at order `180`:

> A finite subset of `ZMod 180` tiles by translation if and only if it is
> spectral.

The release is deliberately limited to this theorem. It does not include the
separate `Z/2310Z` campaign or unfinished generalizations.

- **Author:** Javier Emilio Bazán Sanchez
- **Affiliation:** Facultad de Ciencias, Universidad Nacional Autónoma de México (UNAM)
- **Contact:** [bazan@ciencias.unam.mx](mailto:bazan@ciencias.unam.mx)
- **Lean:** `v4.31.0`
- **mathlib:** `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`

## Main theorem

The public endpoint is
[`Fuglede.z180_tiles_iff_spectral`](fuglede_lean/Fuglede/Z180FugledeTheorem.lean):

```lean
theorem z180_tiles_iff_spectral (A : Finset (ZMod 180)) :
    (∃ B : Finset (ZMod 180), Tiles A B) ↔
      ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L
```

`Tiles A B` means that the addition map
`A × B → ZMod 180`, `(a,b) ↦ a+b`, is bijective. Thus every group element has
one and only one representation.

`CyclotomicSpectrum 180 A L` is an exact algebraic encoding of a Fourier
spectrum. The development proves that it is equivalent to the usual condition
that the characters indexed by `L` form an orthogonal basis on `A`; it is not
an approximation or a weaker proxy.

## Proof structure

The two implications are checked independently.

### Spectral implies tiling

A cardinality and divisor reduction closes all branches except `|A| = 30`.
The final branch combines:

1. a projective-profile audit that compresses 16,796 literal pairs to 213
   exact profile cells, refutes 16,574 pairs, and links the remaining 222 to
   explicit catalogue witnesses;
2. a common-frame certificate for the coupled five-row Gram data;
3. the V81/V96 assembly that feeds this certificate into the global reduction.

The component endpoint is
[`z180_exists_tiling_of_spectral_v96`](fuglede_lean/Fuglede/Z180K30UnconditionalCatalogueClosureV96.lean).

### Tiling implies spectral

A general Fourier theorem characterizes a tiling pair by the cardinality
identity and an exact zero cover at every nonzero frequency. Since the size of
a tile divides `180`, the proof closes the eighteen possible cardinalities by
endpoint arguments, prime-power allocation, cyclotomic forcing, and quotient
descent.

The final `|A| = 30` case has a six-point complement. It is dilated by five and
projected to `ZMod 36`; a checked six-frequency construction in `ZMod 36` is
then lifted through the five fibres of `ZMod 180 → ZMod 36` to produce a
30-point spectrum.

The component endpoint is
[`z180_exists_spectrum_of_tile_v12`](fuglede_lean/Fuglede/Z180TilingSpectralClosureV12.lean).

See [`docs/PROOF_MAP.md`](docs/PROOF_MAP.md) for a file-level map.

## What counts as a certificate

All proof-relevant finite certificates are ordinary `.lean` source files in
the transitive import closure of `Z180FugledeTheorem`. They are elaborated by
Lean and replayed by its kernel; no Python script, SMT solver, floating-point
calculation, or precompiled object is trusted by the theorem.

The release contains exactly the local source closure needed by the endpoint:

- 2,411 Lean modules;
- 25,405,989 bytes and 294,748 source lines at release preparation time;
- zero missing local imports;
- zero `sorry`, `admit`, project-defined axioms, `unsafe`, or `native_decide`
  in the closure.

Every proof input is authenticated in
[`verification/Z180_RELEASE_SHA256.txt`](verification/Z180_RELEASE_SHA256.txt).
The files under [`scripts/`](scripts/) and [`certificates/`](certificates/) are
supplementary provenance for the largest generated V97 sub-DAG. They are not
part of the logical trust base.

## Reproduce the theorem

Install Git and [elan](https://github.com/leanprover/elan). Python is optional:
it audits release manifests but is not needed by the kernel build. Then run:

```bash
git clone https://github.com/asim-v/fuglede-z180-formal.git
cd fuglede-z180-formal/fuglede_lean
lake update
lake exe cache get
lake build '+Fuglede.Z180FugledeTheorem:olean'
lake env leanchecker -v Fuglede.Z180FugledeTheorem
cd ..
```

The final `#print axioms` report should contain only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

These are standard classical and quotient principles used by mathlib. No
problem-specific axiom is introduced.

To reconstruct the import closure, scan it for proof escape hatches, and
authenticate all 2,415 release inputs:

```bash
python scripts/audit_z180_release.py
```

To authenticate the supplemental deterministic V97 source manifest
separately:

```bash
python scripts/generate_z180_k30_projective_profile_audit_v97.py
```

On Windows, a serialized low-memory replay is available as:

```powershell
powershell -ExecutionPolicy Bypass `
  -File scripts/run_z180_k30_projective_profile_audit_v97.ps1
```

Detailed commands and the trust boundary are recorded in
[`verification/README.md`](verification/README.md).

## Article

The two-column manuscript is in [`paper/main.tex`](paper/main.tex), with its
bibliography in [`paper/references.bib`](paper/references.bib). The rendered
artifact is [`paper/main.pdf`](paper/main.pdf).

Build it with a conventional TeX distribution:

```bash
cd paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Repository map

| Path | Purpose |
| --- | --- |
| [`paper/`](paper/) | Article source, bibliography, and rendered PDF |
| [`fuglede_lean/`](fuglede_lean/) | Pinned, self-contained Lean project |
| [`fuglede_lean/Fuglede/`](fuglede_lean/Fuglede/) | Exact source closure of the final theorem |
| [`docs/PROOF_MAP.md`](docs/PROOF_MAP.md) | Mathematical-to-formal proof map |
| [`verification/`](verification/) | Reproduction commands and trust boundary |
| [`scripts/`](scripts/) | Optional provenance and replay tools for V97 |
| [`certificates/`](certificates/) | Small external inputs for those provenance tools |

## Scope and literature

This is a theorem about the single finite cyclic group `ZMod 180`, not about
all cyclic groups, arbitrary finite abelian groups, or Euclidean Fuglede.
Order `180 = 2²·3²·5` lies in the three-prime, two-repeated-prime regime. The
article explains how the result relates to existing cyclic-group families and
does not claim that the converse direction was previously unknown.

## License and citation

The Lean code, repository documentation, manuscript source, and rendered
article are released under the MIT License.
Citation metadata are in [`CITATION.cff`](CITATION.cff).
