import Fuglede.Z180K12M6HighOrderRemainderDefs
import Fuglede.Z180K12M6HighOrderRemoved
import Mathlib.Tactic

/-! # Integral projected remainder coefficients for order thirty-six -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The twelve explicit forms are exactly the coefficients of the monic
`Phi_36` remainder. -/
theorem projection36_phi36_remainder_coeffs_high (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 36 b 0 = projection36Phi36R0 b ∧
    projection36CyclotomicRemainderCoeff 36 b 1 = projection36Phi36R1 b ∧
    projection36CyclotomicRemainderCoeff 36 b 2 = projection36Phi36R2 b ∧
    projection36CyclotomicRemainderCoeff 36 b 3 = projection36Phi36R3 b ∧
    projection36CyclotomicRemainderCoeff 36 b 4 = projection36Phi36R4 b ∧
    projection36CyclotomicRemainderCoeff 36 b 5 = projection36Phi36R5 b ∧
    projection36CyclotomicRemainderCoeff 36 b 6 = projection36Phi36R6 b ∧
    projection36CyclotomicRemainderCoeff 36 b 7 = projection36Phi36R7 b ∧
    projection36CyclotomicRemainderCoeff 36 b 8 = projection36Phi36R8 b ∧
    projection36CyclotomicRemainderCoeff 36 b 9 = projection36Phi36R9 b ∧
    projection36CyclotomicRemainderCoeff 36 b 10 = projection36Phi36R10 b ∧
    projection36CyclotomicRemainderCoeff 36 b 11 = projection36Phi36R11 b := by
  let r := projection36RemainderRemoved 36 b
  have hdiv : cyclotomic 36 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 36 b (by
      rw [show Nat.totient 36 = 12 by decide]
      norm_num)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    projection36_phi36_remainders r (by
      simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 12 ≤ j) :
      projection36CyclotomicRemainderCoeff 36 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 36 = 12 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi36R0, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R1, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R2, r,
      projection36RemainderRemoved] at h2 ⊢
    norm_num [hz] at h2 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R3, r,
      projection36RemainderRemoved] at h3 ⊢
    norm_num [hz] at h3 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R4, r,
      projection36RemainderRemoved] at h4 ⊢
    norm_num [hz] at h4 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R5, r,
      projection36RemainderRemoved] at h5 ⊢
    norm_num [hz] at h5 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R6, r,
      projection36RemainderRemoved] at h6 ⊢
    norm_num [hz] at h6 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R7, r,
      projection36RemainderRemoved] at h7 ⊢
    norm_num [hz] at h7 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R8, r,
      projection36RemainderRemoved] at h8 ⊢
    norm_num [hz] at h8 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R9, r,
      projection36RemainderRemoved] at h9 ⊢
    norm_num [hz] at h9 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi36R10, r,
      projection36RemainderRemoved] at h10 ⊢
    norm_num [hz] at h10 ⊢
    linarith
  · dsimp only [projection36Phi36R11, r,
      projection36RemainderRemoved] at h11 ⊢
    norm_num [hz] at h11 ⊢
    linarith

/-- Zero explicit remainders recover integral `Phi_36` divisibility. -/
theorem cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero_high
    (b : Fin 36 → Int)
    (hz : projection36Phi36R0 b = 0 ∧ projection36Phi36R1 b = 0 ∧
      projection36Phi36R2 b = 0 ∧ projection36Phi36R3 b = 0 ∧
      projection36Phi36R4 b = 0 ∧ projection36Phi36R5 b = 0 ∧
      projection36Phi36R6 b = 0 ∧ projection36Phi36R7 b = 0 ∧
      projection36Phi36R8 b = 0 ∧ projection36Phi36R9 b = 0 ∧
      projection36Phi36R10 b = 0 ∧ projection36Phi36R11 b = 0) :
    cyclotomic 36 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩
  rcases projection36_phi36_remainder_coeffs_high b with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  rw [show Nat.totient 36 = 12 by decide] at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3
  · exact h4.trans z4
  · exact h5.trans z5
  · exact h6.trans z6
  · exact h7.trans z7
  · exact h8.trans z8
  · exact h9.trans z9
  · exact h10.trans z10
  · exact h11.trans z11

#print axioms projection36_phi36_remainder_coeffs_high
#print axioms cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero_high

end Z180K12HighOrder

end Fuglede
