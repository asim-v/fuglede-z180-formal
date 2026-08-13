import Fuglede.Z180K12M6Order20Phi6Grouping
import Mathlib.Tactic

/-!
# Difference form of the projected order-six bridge
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

theorem projection36IndicatorMask_sub_order20
    (b b' : Fin 36 → Int) :
    projection36IndicatorMask (fun i ↦ b i - b' i) =
      projection36IndicatorMask b - projection36IndicatorMask b' := by
  rw [projection36IndicatorMask, projection36IndicatorMask,
    projection36IndicatorMask, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [monomial_sub]

/-- Divisibility of the difference of two projected masks makes their two
explicit `Phi_6` count remainders equal. -/
theorem projection36_phi6_count12_eq_of_sub_dvd_order20
    (b b' : Fin 36 → Int)
    (hdiv : cyclotomic 6 Int ∣
      projection36IndicatorMask b - projection36IndicatorMask b') :
    z180K12Order20Phi6R0 (projection36Count12 b) =
        z180K12Order20Phi6R0 (projection36Count12 b') ∧
    z180K12Order20Phi6R1 (projection36Count12 b) =
        z180K12Order20Phi6R1 (projection36Count12 b') := by
  have hdiv' : cyclotomic 6 Int ∣
      projection36IndicatorMask (fun i ↦ b i - b' i) := by
    rw [projection36IndicatorMask_sub_order20]
    exact hdiv
  obtain ⟨h0, h1⟩ :=
    (projection36_phi6_dvd_iff_remainders_zero
      (fun i ↦ b i - b' i)).1 hdiv'
  have hb := projection36_phi6_count12_remainders_order20 b
  have hb' := projection36_phi6_count12_remainders_order20 b'
  rw [hb.1, hb'.1, hb.2, hb'.2]
  dsimp only [projection36Phi6R0, projection36Phi6R1] at h0 h1 ⊢
  constructor <;> linarith

#print axioms projection36_phi6_count12_eq_of_sub_dvd_order20

end Fuglede
