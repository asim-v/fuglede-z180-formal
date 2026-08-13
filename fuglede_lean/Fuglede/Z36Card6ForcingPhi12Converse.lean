import Fuglede.Z180K12M6HighOrderRemainders
import Mathlib.Tactic

/-! A small converse from the four concrete `Phi_12` remainders. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem z36_remainderCoeff_twelve (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 12 b 0 = projection36Phi12R0 b ∧
    projection36CyclotomicRemainderCoeff 12 b 1 = projection36Phi12R1 b ∧
    projection36CyclotomicRemainderCoeff 12 b 2 = projection36Phi12R2 b ∧
    projection36CyclotomicRemainderCoeff 12 b 3 = projection36Phi12R3 b := by
  simp only [projection36CyclotomicRemainderCoeff_eq_sum]
  norm_num [Fin.sum_univ_succ, cyclotomic_twelve_eq_int,
    projection36Phi12R0, projection36Phi12R1,
    projection36Phi12R2, projection36Phi12R3,
    projection36Count12]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem z36_cyclotomic_twelve_dvd_projection36Indicator_of_remainders_zero
    (b : Fin 36 → Int)
    (hz : projection36Phi12R0 b = 0 ∧ projection36Phi12R1 b = 0 ∧
      projection36Phi12R2 b = 0 ∧ projection36Phi12R3 b = 0) :
    cyclotomic 12 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3⟩
  rcases z36_remainderCoeff_twelve b with ⟨h0, h1, h2, h3⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  norm_num at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3

#print axioms z36_cyclotomic_twelve_dvd_projection36Indicator_of_remainders_zero

end Fuglede
