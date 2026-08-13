import Fuglede.Z180K12M6HighOrderRemainderDefs
import Fuglede.Z180K12M6HighOrderRemoved
import Mathlib.Tactic

/-!
# Characteristic-five projected remainders for order nine

This shard contains the bounded integral argument used by the order-forty-five
branch of the exact `k = 12` sieve.
-/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem remainderCoeff_nine_high (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 9 b 0 = projection36Phi9R0 b ∧
    projection36CyclotomicRemainderCoeff 9 b 1 = projection36Phi9R1 b ∧
    projection36CyclotomicRemainderCoeff 9 b 2 = projection36Phi9R2 b ∧
    projection36CyclotomicRemainderCoeff 9 b 3 = projection36Phi9R3 b ∧
    projection36CyclotomicRemainderCoeff 9 b 4 = projection36Phi9R4 b ∧
    projection36CyclotomicRemainderCoeff 9 b 5 = projection36Phi9R5 b := by
  let r := projection36RemainderRemoved 9 b
  have hdiv : cyclotomic 9 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 9 b (by
      rw [show Nat.totient 9 = 6 by decide]
      norm_num)
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := projection36_phi9_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 6 ≤ j) :
      projection36CyclotomicRemainderCoeff 9 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 9 = 6 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi9R0, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi9R1, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi9R2, r,
      projection36RemainderRemoved] at h2 ⊢
    norm_num [hz] at h2 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi9R3, r,
      projection36RemainderRemoved] at h3 ⊢
    norm_num [hz] at h3 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi9R4, r,
      projection36RemainderRemoved] at h4 ⊢
    norm_num [hz] at h4 ⊢
    linarith
  · dsimp only [projection36Phi9R5, r,
      projection36RemainderRemoved] at h5 ⊢
    norm_num [hz] at h5 ⊢
    linarith

private theorem signed_four_four_five_mul_eq_zero_nine
    (a b c d e f g h k : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (heq : a - b + d - c + e - f + h - g = 5 * k) :
    a - b + d - c + e - f + h - g = 0 := by
  omega

/-- A mapped `Phi_9` divisor forces the six bounded integral remainders to
vanish. -/
theorem projection36_phi9_remainders_zero_of_mod_five_dvd_high
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hdiv : cyclotomic 9 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    projection36Phi9R0 b = 0 ∧ projection36Phi9R1 b = 0 ∧
    projection36Phi9R2 b = 0 ∧ projection36Phi9R3 b = 0 ∧
    projection36Phi9R4 b = 0 ∧ projection36Phi9R5 b = 0 := by
  rcases remainderCoeff_nine_high b with ⟨h0, h1, h2, h3, h4, h5⟩
  obtain ⟨k0, hk0⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  obtain ⟨k2, hk2⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 2
  obtain ⟨k3, hk3⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 3
  obtain ⟨k4, hk4⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 4
  obtain ⟨k5, hk5⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 5
  rw [h0] at hk0
  rw [h1] at hk1
  rw [h2] at hk2
  rw [h3] at hk3
  rw [h4] at hk4
  rw [h5] at hk5
  dsimp only [projection36Phi9R0] at hk0
  dsimp only [projection36Phi9R1] at hk1
  dsimp only [projection36Phi9R2] at hk2
  dsimp only [projection36Phi9R3] at hk3
  dsimp only [projection36Phi9R4] at hk4
  dsimp only [projection36Phi9R5] at hk5
  dsimp only [projection36Phi9R0, projection36Phi9R1,
    projection36Phi9R2, projection36Phi9R3,
    projection36Phi9R4, projection36Phi9R5]
  constructor
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 0) (b 6) (b 15) (b 9) (b 18) (b 24) (b 33) (b 27) k0
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk0])
  constructor
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 1) (b 7) (b 16) (b 10) (b 19) (b 25) (b 34) (b 28) k1
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk1])
  constructor
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 2) (b 8) (b 17) (b 11) (b 20) (b 26) (b 35) (b 29) k2
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk2])
  constructor
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 3) (b 6) (b 15) (b 12) (b 21) (b 24) (b 33) (b 30) k3
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk3])
  constructor
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 4) (b 7) (b 16) (b 13) (b 22) (b 25) (b 34) (b 31) k4
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk4])
  · exact signed_four_four_five_mul_eq_zero_nine
      (b 5) (b 8) (b 17) (b 14) (b 23) (b 26) (b 35) (b 32) k5
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk5])

/-- Zero explicit remainders recover integral `Phi_9` divisibility. -/
theorem cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero_high
    (b : Fin 36 → Int)
    (hz : projection36Phi9R0 b = 0 ∧ projection36Phi9R1 b = 0 ∧
      projection36Phi9R2 b = 0 ∧ projection36Phi9R3 b = 0 ∧
      projection36Phi9R4 b = 0 ∧ projection36Phi9R5 b = 0) :
    cyclotomic 9 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3, z4, z5⟩
  rcases remainderCoeff_nine_high b with ⟨h0, h1, h2, h3, h4, h5⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  rw [show Nat.totient 9 = 6 by decide] at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3
  · exact h4.trans z4
  · exact h5.trans z5

#print axioms projection36_phi9_remainders_zero_of_mod_five_dvd_high
#print axioms cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero_high

end Z180K12HighOrder

end Fuglede
