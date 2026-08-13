import Fuglede.Z180K30ExceptionalStarOrbitDefsV4
import Mathlib.Tactic

/-!
# Coupled affine-orbit signature audit for the K30 exceptional star (V78)

This module contains only the small, reusable definitions behind the 56
generated audit leaves.  A leaf fixes a column orbit `o` and a row orbit `r`,
enumerates the 12 * 36 affine images of the row representative, retains the
images whose exact raw trace square is 936 against the fixed column
representative, and checks that the relevant Gram signature occurs in the
existing star-candidate list for `o`.

The affine parameters are deliberately shared at the caller: this audit is
designed for the coupled five-Gram normalization, not for five independent
pair normalizations.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

/-- The one- or two-coordinate Gram signature used by the non-H obstruction.
For the surviving H orbit the signature is empty. -/
def z180K30StarSignatureV78 (o : Fin 8) (W : RawSet) : List Int :=
  match o with
  | 0 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 0)) 3 0]
  | 1 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 1)) 3 0]
  | 2 =>
      [gramCoefficientV2
          (gram W (z180K30ExceptionalOrbitColumnV4 2)) 2 0,
        gramCoefficientV2
          (gram W (z180K30ExceptionalOrbitColumnV4 2)) 2 6]
  | 3 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 3)) 3 0]
  | 4 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 4)) 3 0]
  | 5 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 5)) 3 0]
  | 6 =>
      [gramCoefficientV2
        (gram W (z180K30ExceptionalOrbitColumnV4 6)) 2 0]
  | 7 => []

/-- A row set is covered when an existing star candidate has the same exact
signature in the fixed normalized column frame. -/
def z180K30SignatureCoveredBV78 (o : Fin 8) (W : RawSet) : Bool :=
  (z180K30ExceptionalOrbitChoicesV4 o).any fun candidate =>
    z180K30StarSignatureV78 o W ==
      z180K30StarSignatureV78 o candidate

/-- The 432 affine presentations of the `r`-th row-orbit representative.
Duplicates are intentionally retained: every generated leaf has the same
fixed enumeration size and directly mirrors the Boolean affine search. -/
def z180K30OrbitImagesV78 (r : Fin 8) : List RawSet :=
  units36.flatMap fun unit =>
    rawUniverse.map fun translation =>
      affineSet unit translation (z180K30ExceptionalOrbitColumnV4 r)

/-- Exact finite audit for one normalized column orbit and one source row
orbit. -/
def z180K30OrbitSignatureAuditV78 (o r : Fin 8) : BatchAudit :=
  let candidates := z180K30OrbitImagesV78 r
  let accepted := candidates.filter fun W =>
    gramTraceSquare W (z180K30ExceptionalOrbitColumnV4 o) ==
      scalarCoeff 936
  {
    enumerated := candidates.length
    accepted := accepted.length
    uncovered := (accepted.filter fun W =>
      !(z180K30SignatureCoveredBV78 o W)).length
  }

/-- Logical semantics of a zero-uncovered V78 leaf. -/
theorem z180K30OrbitSignatureAudit_uncovered_zero_semanticsV78
    (o r : Fin 8)
    (hzero : (z180K30OrbitSignatureAuditV78 o r).uncovered = 0)
    (W : RawSet)
    (hmem : W ∈ z180K30OrbitImagesV78 r)
    (htrace :
      gramTraceSquare W (z180K30ExceptionalOrbitColumnV4 o) =
        scalarCoeff 936) :
    z180K30SignatureCoveredBV78 o W = true := by
  let candidates := z180K30OrbitImagesV78 r
  let accepted := candidates.filter fun candidate =>
    gramTraceSquare candidate (z180K30ExceptionalOrbitColumnV4 o) ==
      scalarCoeff 936
  let uncovered := accepted.filter fun candidate =>
    !(z180K30SignatureCoveredBV78 o candidate)
  have huncoveredLength : uncovered.length = 0 := by
    simpa only [z180K30OrbitSignatureAuditV78, candidates,
      accepted, uncovered] using hzero
  have huncoveredNil : uncovered = [] := by
    simpa using huncoveredLength
  by_contra hcovered
  have hcoveredFalse : z180K30SignatureCoveredBV78 o W = false := by
    exact Bool.eq_false_of_not_eq_true hcovered
  have hbad : (!(z180K30SignatureCoveredBV78 o W)) = true := by
    simp only [hcoveredFalse, Bool.not_false]
  have hmemAccepted : W ∈ accepted := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    simp only [htrace, beq_self_eq_true]
  have hmemUncovered : W ∈ uncovered := by
    exact List.mem_filter.mpr ⟨hmemAccepted, hbad⟩
  simpa only [huncoveredNil, List.not_mem_nil] using hmemUncovered

/-- Boolean coverage exposes an actual candidate with equal signature. -/
theorem z180K30SignatureCoveredBV78_iff
    (o : Fin 8) (W : RawSet) :
    z180K30SignatureCoveredBV78 o W = true ↔
      ∃ candidate ∈ z180K30ExceptionalOrbitChoicesV4 o,
        z180K30StarSignatureV78 o W =
          z180K30StarSignatureV78 o candidate := by
  simp only [z180K30SignatureCoveredBV78, List.any_eq_true,
    beq_iff_eq]

#print axioms z180K30OrbitSignatureAudit_uncovered_zero_semanticsV78
#print axioms z180K30SignatureCoveredBV78_iff

end Fuglede.Z180K30ExceptionalRawV2
