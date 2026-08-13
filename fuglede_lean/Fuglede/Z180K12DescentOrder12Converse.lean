import Fuglede.Z180K12M6HighOrderRemainderDefs
import Fuglede.Z180K12M6HighOrderRemoved
import Mathlib.Tactic

/-!
# Integral converse for the four explicit `Phi_12` remainders

The order-twelve high-order shard only needed the forward coefficient
identities privately.  Direct cardinality-twelve descent also needs the
converse: if all four explicit remainders vanish, the projected indicator
mask is integrally divisible by `Phi_12`.  This module exposes exactly that
small bridge and nothing from the order-sixty semantic exclusion.
-/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The first four monic-remainder coefficients are the explicit
`Phi_12` remainder forms. -/
theorem projection36_phi12_remainder_coeffs_direct (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 12 b 0 = projection36Phi12R0 b ∧
    projection36CyclotomicRemainderCoeff 12 b 1 = projection36Phi12R1 b ∧
    projection36CyclotomicRemainderCoeff 12 b 2 = projection36Phi12R2 b ∧
    projection36CyclotomicRemainderCoeff 12 b 3 = projection36Phi12R3 b := by
  let r := projection36RemainderRemoved 12 b
  have hdiv : cyclotomic 12 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 12 b (by
      rw [show Nat.totient 12 = 4 by decide]
      norm_num)
  obtain ⟨h0, h1, h2, h3⟩ := projection36_phi12_count12_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 4 ≤ j) :
      projection36CyclotomicRemainderCoeff 12 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 12 = 4 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi12R0, projection36Count12, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi12R1, projection36Count12, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi12R2, projection36Count12, r,
      projection36RemainderRemoved] at h2 ⊢
    norm_num [hz] at h2 ⊢
    linarith
  · dsimp only [projection36Phi12R3, projection36Count12, r,
      projection36RemainderRemoved] at h3 ⊢
    norm_num [hz] at h3 ⊢
    linarith

/-- Vanishing of the four explicit remainders reconstructs integral
`Phi_12` divisibility of the projected indicator mask. -/
theorem cyclotomic_twelve_dvd_projection36Indicator_of_remainders_zero_direct
    (b : Fin 36 → Int)
    (hz : projection36Phi12R0 b = 0 ∧ projection36Phi12R1 b = 0 ∧
      projection36Phi12R2 b = 0 ∧ projection36Phi12R3 b = 0) :
    cyclotomic 12 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3⟩
  rcases projection36_phi12_remainder_coeffs_direct b with ⟨h0, h1, h2, h3⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  rw [show Nat.totient 12 = 4 by decide] at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3

#print axioms projection36_phi12_remainder_coeffs_direct
#print axioms cyclotomic_twelve_dvd_projection36Indicator_of_remainders_zero_direct

end Z180K12HighOrder

end Fuglede
