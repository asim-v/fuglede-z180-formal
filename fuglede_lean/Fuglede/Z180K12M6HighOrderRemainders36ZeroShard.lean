import Fuglede.Z180K12M6HighOrderRemainders36CoeffShard
import Mathlib.Tactic

/-! # Characteristic-five bounded remainder kernel for order thirty-six -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem signed_two_two_five_mul_eq_zero_thirtysix
    (a b c d k : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (heq : a - b - c + d = 5 * k) : a - b - c + d = 0 := by
  omega

/-- A mapped `Phi_36` divisor forces all twelve bounded integral remainder
coordinates to vanish. -/
theorem projection36_phi36_remainders_zero_of_mod_five_dvd_high
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hdiv : cyclotomic 36 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    projection36Phi36R0 b = 0 ∧ projection36Phi36R1 b = 0 ∧
    projection36Phi36R2 b = 0 ∧ projection36Phi36R3 b = 0 ∧
    projection36Phi36R4 b = 0 ∧ projection36Phi36R5 b = 0 ∧
    projection36Phi36R6 b = 0 ∧ projection36Phi36R7 b = 0 ∧
    projection36Phi36R8 b = 0 ∧ projection36Phi36R9 b = 0 ∧
    projection36Phi36R10 b = 0 ∧ projection36Phi36R11 b = 0 := by
  rcases projection36_phi36_remainder_coeffs_high b with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  obtain ⟨k0, hk0⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  obtain ⟨k2, hk2⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 2
  obtain ⟨k3, hk3⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 3
  obtain ⟨k4, hk4⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 4
  obtain ⟨k5, hk5⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 5
  obtain ⟨k6, hk6⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 6
  obtain ⟨k7, hk7⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 7
  obtain ⟨k8, hk8⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 8
  obtain ⟨k9, hk9⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 9
  obtain ⟨k10, hk10⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 10
  obtain ⟨k11, hk11⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 11
  rw [h0] at hk0
  rw [h1] at hk1
  rw [h2] at hk2
  rw [h3] at hk3
  rw [h4] at hk4
  rw [h5] at hk5
  rw [h6] at hk6
  rw [h7] at hk7
  rw [h8] at hk8
  rw [h9] at hk9
  rw [h10] at hk10
  rw [h11] at hk11
  dsimp only [projection36Phi36R0, projection36Phi36R1,
    projection36Phi36R2, projection36Phi36R3,
    projection36Phi36R4, projection36Phi36R5,
    projection36Phi36R6, projection36Phi36R7,
    projection36Phi36R8, projection36Phi36R9,
    projection36Phi36R10, projection36Phi36R11]
    at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8 hk9 hk10 hk11 ⊢
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 0) (b 12) (b 18) (b 30) k0
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk0
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 1) (b 13) (b 19) (b 31) k1
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk1
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 2) (b 14) (b 20) (b 32) k2
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk2
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 3) (b 15) (b 21) (b 33) k3
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk3
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 4) (b 16) (b 22) (b 34) k4
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk4
  constructor
  · exact signed_two_two_five_mul_eq_zero_thirtysix
      (b 5) (b 17) (b 23) (b 35) k5
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk5
  constructor
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 6) (b 24) (b 30) (b 12) k6
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk6])
    linarith only [h]
  constructor
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 7) (b 25) (b 31) (b 13) k7
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk7])
    linarith only [h]
  constructor
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 8) (b 26) (b 32) (b 14) k8
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk8])
    linarith only [h]
  constructor
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 9) (b 27) (b 33) (b 15) k9
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk9])
    linarith only [h]
  constructor
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 10) (b 28) (b 34) (b 16) k10
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk10])
    linarith only [h]
  · have h := signed_two_two_five_mul_eq_zero_thirtysix
      (b 11) (b 29) (b 35) (b 17) k11
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk11])
    linarith only [h]

#print axioms projection36_phi36_remainders_zero_of_mod_five_dvd_high

end Z180K12HighOrder

end Fuglede
