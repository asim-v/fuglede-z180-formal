import Fuglede.Z180K12M6HighOrderRemainderDefs
import Fuglede.Z180K12M6HighOrderRemoved
import Mathlib.Tactic

/-!
# Integral converse for the two explicit `Phi_3` remainders
-/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The first two monic-remainder coefficients are the explicit `Phi_3`
remainder forms. -/
theorem projection36_phi3_remainder_coeffs_direct (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 3 b 0 = projection36Phi3R0 b ∧
    projection36CyclotomicRemainderCoeff 3 b 1 = projection36Phi3R1 b := by
  let r := projection36RemainderRemoved 3 b
  have hdiv : cyclotomic 3 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 3 b (by
      rw [show Nat.totient 3 = 2 by decide]
      norm_num)
  obtain ⟨h0, h1⟩ := projection36_phi3_count12_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 2 ≤ j) :
      projection36CyclotomicRemainderCoeff 3 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 3 = 2 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi3R0, projection36Count12, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  · dsimp only [projection36Phi3R1, projection36Count12, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith

/-- Vanishing of the two explicit remainders reconstructs integral `Phi_3`
divisibility of the projected indicator mask. -/
theorem cyclotomic_three_dvd_projection36Indicator_of_remainders_zero_direct
    (b : Fin 36 → Int)
    (hz : projection36Phi3R0 b = 0 ∧ projection36Phi3R1 b = 0) :
    cyclotomic 3 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1⟩
  rcases projection36_phi3_remainder_coeffs_direct b with ⟨h0, h1⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  rw [show Nat.totient 3 = 2 by decide] at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1

#print axioms projection36_phi3_remainder_coeffs_direct
#print axioms cyclotomic_three_dvd_projection36Indicator_of_remainders_zero_direct

end Z180K12HighOrder

end Fuglede
