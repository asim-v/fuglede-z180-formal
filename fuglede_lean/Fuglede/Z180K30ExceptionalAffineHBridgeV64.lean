import Fuglede.Z180K30ExceptionalRawCoreV2
import Fuglede.Z180K30ExceptionalHGramWitness
import Mathlib.Tactic

/-!
# Affine invariance of the exceptional H-coset condition

This is a semantic bridge from the raw affine-orbit predicate to the raw
H-coset predicate. It does not use evaluation by `native_decide`.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem HCosetB_of_valid_affine_H_v64
    (V : RawSet)
    (hv : validSixSetB V = true)
    (ha : affineEquivalentB V z180K30ExceptionalH = true) :
    HCosetB V = true := by
  rw [affineEquivalentB] at ha
  rcases List.any_eq_true.mp ha with ⟨unit, hunit, ha⟩
  rcases List.any_eq_true.mp ha with
    ⟨translation, _htranslation, hsetEq⟩
  have hImageAll :
      (affineSet unit translation V).all
        (fun point => decide (point ∈ z180K30ExceptionalH)) = true :=
    (Bool.and_eq_true.mp hsetEq).2
  have hImageInH (point : RawPoint) (hpoint : point ∈ V) :
      affinePoint unit translation point ∈ z180K30ExceptionalH := by
    have hpointImage : affinePoint unit translation point ∈
        affineSet unit translation V := by
      exact List.mem_map.mpr ⟨point, hpoint, rfl⟩
    have hdecide :=
      (List.all_eq_true.mp hImageAll)
        (affinePoint unit translation point) hpointImage
    exact of_decide_eq_true hdecide
  have hHmod : ∀ point ∈ z180K30ExceptionalH,
      point.val % 6 = 0 := by
    decide
  have hImageMod (point : RawPoint) (hpoint : point ∈ V) :
      (affinePoint unit translation point).val % 6 = 0 :=
    hHmod _ (hImageInH point hpoint)
  have hunitCases :
      unit = 1 ∨ unit = 5 ∨ unit = 7 ∨ unit = 11 ∨
      unit = 13 ∨ unit = 17 ∨ unit = 19 ∨ unit = 23 ∨
      unit = 25 ∨ unit = 29 ∨ unit = 31 ∨ unit = 35 := by
    simpa [units36] using hunit
  have hcancel (left right : RawPoint)
      (hleft : (affinePoint unit translation left).val % 6 = 0)
      (hright : (affinePoint unit translation right).val % 6 = 0) :
      left.val % 6 = right.val % 6 := by
    rcases hunitCases with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst unit <;> simp [affinePoint] at hleft hright ⊢ <;> omega
  cases V with
  | nil =>
      simp [validSixSetB] at hv
  | cons base tail =>
      simp only [HCosetB, hv, Bool.true_and]
      apply List.any_eq_true.mpr
      refine ⟨base.val % 6,
        List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
      apply List.all_eq_true.mpr
      intro point hpoint
      have hresidue : point.val % 6 = base.val % 6 :=
        hcancel point base
          (hImageMod point hpoint)
          (hImageMod base (by simp))
      simpa using hresidue

#print axioms HCosetB_of_valid_affine_H_v64

end Fuglede.Z180K30ExceptionalRawV2
