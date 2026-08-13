import Fuglede.Z180K30ExceptionalOrbitFrameExtractionV85Fix3
import Fuglede.Z180K30ExceptionalUnitTraceClassifierV91
import Fuglede.Z180K30FiveGramStarSemanticsV82

/-!
# Exact trace transport into a common K30 affine frame (V92 Fix)

The normalized row uses the inverse unit and zero translation.  The original
row translation is irrelevant to trace, so this is the minimal common-frame
normalization needed by the V91 row-orbit classifier.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30FrameInverseUnitV92Fix (unit : RawPoint) : RawPoint :=
  z180K30UnitInverseV85Fix3 unit

theorem z180K30FrameInverseUnit_memV92Fix
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30FrameInverseUnitV92Fix unit ∈ units36 :=
  z180K30UnitInverseV85Fix3_mem hunit

theorem z180K30FrameInverseUnitProductV92Fix
    {unit : RawPoint} (hunit : unit ∈ units36) :
    z180K30FrameInverseUnitV92Fix unit * unit = 1 := by
  simp only [units36, List.mem_cons, List.mem_singleton] at hunit
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

theorem z180K30FrameUnitInverseProductV92Fix
    {unit : RawPoint} (hunit : unit ∈ units36) :
    unit * z180K30FrameInverseUnitV92Fix unit = 1 := by
  simp only [units36, List.mem_cons, List.mem_singleton] at hunit
  rcases hunit with hunit | hunit | hunit | hunit | hunit | hunit |
      hunit | hunit | hunit | hunit | hunit | hunit <;>
    subst unit <;> decide

@[simp]
theorem affineSet_one_zeroV92Fix (set : RawSet) :
    affineSet 1 0 set = set := by
  induction set with
  | nil => rfl
  | cons point tail ih =>
      simp only [affineSet, List.map_cons]
      have hpoint : affinePoint 1 0 point = point := by
        apply Fin.ext
        simp [affinePoint]
      rw [hpoint]
      exact congrArg (List.cons point) ih

theorem z180K30FrameDilationCancelsV92Fix
    (unit : RawPoint) (set : RawSet)
    (hunit : unit ∈ units36) :
    affineSet unit 0
        (affineSet (z180K30FrameInverseUnitV92Fix unit) 0 set) = set := by
  rw [affineSet_comp_v90, z180K30FrameUnitInverseProductV92Fix hunit]
  simp only [affinePoint, Nat.mul_zero, Nat.zero_mod]
  exact affineSet_one_zeroV92Fix set

theorem z180K30NormalizedTraceV92Fix
    (U V representative : RawSet)
    (unit translation : RawPoint)
    (hunit : unit ∈ units36)
    (hvalidV : validSixSetB V = true)
    (hvalidRepresentative : validSixSetB representative = true)
    (hframe :
      rawSetEqB (affineSet unit translation representative) V = true)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    gramTraceSquare
        (affineSet (z180K30FrameInverseUnitV92Fix unit) 0 U)
        representative = scalarCoeff 936 := by
  let W := affineSet (z180K30FrameInverseUnitV92Fix unit) 0 U
  have hvalidAffine :
      validSixSetB (affineSet unit translation representative) = true :=
    validSixSetB_affine_of_unit_v85Fix3
      unit translation representative hunit hvalidRepresentative
  have hperm :
      (affineSet unit translation representative).Perm V :=
    perm_of_rawSetEqB_of_valid_v88 hvalidAffine hvalidV hframe
  have htraceFrame :
      gramTraceSquare U (affineSet unit translation representative) =
        scalarCoeff 936 := by
    calc
      gramTraceSquare U (affineSet unit translation representative) =
          gramTraceSquare U V :=
        gramTraceSquare_eq_of_perm_right_v88 U hperm
      _ = scalarCoeff 936 := htrace
  have hcovariant := gramTraceSquare_affine_covariant_v90
    W representative unit 0 translation
  have hforward : affineSet unit 0 W = U := by
    dsimp only [W]
    exact z180K30FrameDilationCancelsV92Fix unit U hunit
  rw [hforward] at hcovariant
  exact hcovariant.trans htraceFrame

theorem z180K30NormalizedOrbitCoveredV92Fix
    (U : RawSet) (unit : RawPoint)
    (hunit : unit ∈ units36)
    (hcovered : orbitCoveredB U = true) :
    orbitCoveredB
      (affineSet (z180K30FrameInverseUnitV92Fix unit) 0 U) = true :=
  orbitCoveredB_affine_forward_v90 U
    (z180K30FrameInverseUnitV92Fix unit) 0
    (z180K30FrameInverseUnit_memV92Fix hunit) hcovered

#print axioms z180K30NormalizedTraceV92Fix
#print axioms z180K30NormalizedOrbitCoveredV92Fix

end Fuglede.Z180K30ExceptionalRawV2
