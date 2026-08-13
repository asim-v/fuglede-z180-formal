import Fuglede.Z180K12M6HighOrderRemoved
import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-!
# Concrete integral remainders for the high-order `k = 12` sieve

The definitions below are deliberately small linear forms.  Their equality
with monic polynomial remainders is checked from the 36 concrete monomials;
no root approximation or untrusted computation is used.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def projection36Phi3R0 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 0 - projection36Count12 b 2 +
    projection36Count12 b 3 - projection36Count12 b 5 +
    projection36Count12 b 6 - projection36Count12 b 8 +
    projection36Count12 b 9 - projection36Count12 b 11

def projection36Phi3R1 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 1 - projection36Count12 b 2 +
    projection36Count12 b 4 - projection36Count12 b 5 +
    projection36Count12 b 7 - projection36Count12 b 8 +
    projection36Count12 b 10 - projection36Count12 b 11

def projection36Phi9R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33
def projection36Phi9R1 (b : Fin 36 → Int) : Int :=
  b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34
def projection36Phi9R2 (b : Fin 36 → Int) : Int :=
  b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35
def projection36Phi9R3 (b : Fin 36 → Int) : Int :=
  b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33
def projection36Phi9R4 (b : Fin 36 → Int) : Int :=
  b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34
def projection36Phi9R5 (b : Fin 36 → Int) : Int :=
  b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35

def projection36Phi12R0 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 0 - projection36Count12 b 4 -
    projection36Count12 b 6 + projection36Count12 b 10

def projection36Phi12R1 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 1 - projection36Count12 b 5 -
    projection36Count12 b 7 + projection36Count12 b 11

def projection36Phi12R2 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 2 + projection36Count12 b 4 -
    projection36Count12 b 8 - projection36Count12 b 10

def projection36Phi12R3 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 3 + projection36Count12 b 5 -
    projection36Count12 b 9 - projection36Count12 b 11

def projection36Phi18R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33
def projection36Phi18R1 (b : Fin 36 → Int) : Int :=
  b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34
def projection36Phi18R2 (b : Fin 36 → Int) : Int :=
  b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35
def projection36Phi18R3 (b : Fin 36 → Int) : Int :=
  b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33
def projection36Phi18R4 (b : Fin 36 → Int) : Int :=
  b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34
def projection36Phi18R5 (b : Fin 36 → Int) : Int :=
  b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35

def projection36Phi36R0 (b : Fin 36 → Int) : Int := b 0 - b 12 - b 18 + b 30
def projection36Phi36R1 (b : Fin 36 → Int) : Int := b 1 - b 13 - b 19 + b 31
def projection36Phi36R2 (b : Fin 36 → Int) : Int := b 2 - b 14 - b 20 + b 32
def projection36Phi36R3 (b : Fin 36 → Int) : Int := b 3 - b 15 - b 21 + b 33
def projection36Phi36R4 (b : Fin 36 → Int) : Int := b 4 - b 16 - b 22 + b 34
def projection36Phi36R5 (b : Fin 36 → Int) : Int := b 5 - b 17 - b 23 + b 35
def projection36Phi36R6 (b : Fin 36 → Int) : Int := b 6 + b 12 - b 24 - b 30
def projection36Phi36R7 (b : Fin 36 → Int) : Int := b 7 + b 13 - b 25 - b 31
def projection36Phi36R8 (b : Fin 36 → Int) : Int := b 8 + b 14 - b 26 - b 32
def projection36Phi36R9 (b : Fin 36 → Int) : Int := b 9 + b 15 - b 27 - b 33
def projection36Phi36R10 (b : Fin 36 → Int) : Int := b 10 + b 16 - b 28 - b 34
def projection36Phi36R11 (b : Fin 36 → Int) : Int := b 11 + b 17 - b 29 - b 35

private theorem remainderCoeff_three (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 3 b 0 = projection36Phi3R0 b ∧
    projection36CyclotomicRemainderCoeff 3 b 1 = projection36Phi3R1 b := by
  let r := projection36RemainderRemoved 3 b
  have hdiv : cyclotomic 3 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 3 b (by norm_num)
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

private theorem remainderCoeff_nine (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 9 b 0 = projection36Phi9R0 b ∧
    projection36CyclotomicRemainderCoeff 9 b 1 = projection36Phi9R1 b ∧
    projection36CyclotomicRemainderCoeff 9 b 2 = projection36Phi9R2 b ∧
    projection36CyclotomicRemainderCoeff 9 b 3 = projection36Phi9R3 b ∧
    projection36CyclotomicRemainderCoeff 9 b 4 = projection36Phi9R4 b ∧
    projection36CyclotomicRemainderCoeff 9 b 5 = projection36Phi9R5 b := by
  let r := projection36RemainderRemoved 9 b
  have hdiv : cyclotomic 9 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 9 b (by norm_num)
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

private theorem remainderCoeff_twelve (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 12 b 0 = projection36Phi12R0 b ∧
    projection36CyclotomicRemainderCoeff 12 b 1 = projection36Phi12R1 b ∧
    projection36CyclotomicRemainderCoeff 12 b 2 = projection36Phi12R2 b ∧
    projection36CyclotomicRemainderCoeff 12 b 3 = projection36Phi12R3 b := by
  let r := projection36RemainderRemoved 12 b
  have hdiv : cyclotomic 12 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 12 b (by norm_num)
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

private theorem remainderCoeff_eighteen (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 18 b 0 = projection36Phi18R0 b ∧
    projection36CyclotomicRemainderCoeff 18 b 1 = projection36Phi18R1 b ∧
    projection36CyclotomicRemainderCoeff 18 b 2 = projection36Phi18R2 b ∧
    projection36CyclotomicRemainderCoeff 18 b 3 = projection36Phi18R3 b ∧
    projection36CyclotomicRemainderCoeff 18 b 4 = projection36Phi18R4 b ∧
    projection36CyclotomicRemainderCoeff 18 b 5 = projection36Phi18R5 b := by
  let r := projection36RemainderRemoved 18 b
  have hdiv : cyclotomic 18 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 18 b (by norm_num)
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := projection36_phi18_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 6 ≤ j) :
      projection36CyclotomicRemainderCoeff 18 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 18 = 6 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi18R0, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi18R1, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi18R2, r,
      projection36RemainderRemoved] at h2 ⊢
    norm_num [hz] at h2 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi18R3, r,
      projection36RemainderRemoved] at h3 ⊢
    norm_num [hz] at h3 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi18R4, r,
      projection36RemainderRemoved] at h4 ⊢
    norm_num [hz] at h4 ⊢
    linarith
  · dsimp only [projection36Phi18R5, r,
      projection36RemainderRemoved] at h5 ⊢
    norm_num [hz] at h5 ⊢
    linarith

private theorem remainderCoeff_thirtysix (b : Fin 36 → Int) :
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
    cyclotomic_dvd_projection36RemainderRemoved 36 b (by norm_num)
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

private theorem signed_four_four_five_mul_eq_zero
    (a b c d e f g h k : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (heq : a - b - c + d + e - f - g + h = 5 * k) :
    a - b - c + d + e - f - g + h = 0 := by
  omega

private theorem signed_two_two_five_mul_eq_zero
    (a b c d k : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (heq : a - b - c + d = 5 * k) : a - b - c + d = 0 := by
  omega

/-- Characteristic-five `Phi_3` divisibility in the two count coordinates. -/
theorem projection36_phi3_five_multipliers
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 3 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 : Int,
      projection36Phi3R0 b = 5 * k0 ∧
      projection36Phi3R1 b = 5 * k1 := by
  obtain ⟨k0, hk0⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  rcases remainderCoeff_three b with ⟨h0, h1⟩
  exact ⟨k0, k1, h0.symm.trans hk0, h1.symm.trans hk1⟩

/-- A mapped `Phi_9` divisor forces the six short integral remainders to
vanish, since each lies strictly between `-5` and `5`. -/
theorem projection36_phi9_remainders_zero_of_mod_five_dvd
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hdiv : cyclotomic 9 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    projection36Phi9R0 b = 0 ∧ projection36Phi9R1 b = 0 ∧
    projection36Phi9R2 b = 0 ∧ projection36Phi9R3 b = 0 ∧
    projection36Phi9R4 b = 0 ∧ projection36Phi9R5 b = 0 := by
  rcases remainderCoeff_nine b with ⟨h0, h1, h2, h3, h4, h5⟩
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
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 0) (b 6) (b 15) (b 9) (b 18) (b 24) (b 33) (b 27) k0
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk0])
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 1) (b 7) (b 16) (b 10) (b 19) (b 25) (b 34) (b 28) k1
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk1])
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 2) (b 8) (b 17) (b 11) (b 20) (b 26) (b 35) (b 29) k2
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk2])
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 3) (b 6) (b 15) (b 12) (b 21) (b 24) (b 33) (b 30) k3
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk3])
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 4) (b 7) (b 16) (b 13) (b 22) (b 25) (b 34) (b 31) k4
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk4])
  · exact signed_four_four_five_mul_eq_zero
      (b 5) (b 8) (b 17) (b 14) (b 23) (b 26) (b 35) (b 32) k5
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk5])

/-- `Phi_12` divisibility after reduction modulo five makes the four
integral remainder coordinates multiples of five. -/
theorem projection36_phi12_five_multipliers
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 12 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 k2 k3 : Int,
      projection36Phi12R0 b = 5 * k0 ∧
      projection36Phi12R1 b = 5 * k1 ∧
      projection36Phi12R2 b = 5 * k2 ∧
      projection36Phi12R3 b = 5 * k3 := by
  obtain ⟨k0, hk0⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  obtain ⟨k2, hk2⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 2
  obtain ⟨k3, hk3⟩ := projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 3
  rcases remainderCoeff_twelve b with ⟨h0, h1, h2, h3⟩
  exact ⟨k0, k1, k2, k3, h0.symm.trans hk0, h1.symm.trans hk1,
    h2.symm.trans hk2, h3.symm.trans hk3⟩

/-- The order-18 remainder forms are so short that a multiple of five is
forced to be zero for a zero-one indicator. -/
theorem projection36_phi18_remainders_zero_of_mod_five_dvd
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hdiv : cyclotomic 18 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    projection36Phi18R0 b = 0 ∧ projection36Phi18R1 b = 0 ∧
    projection36Phi18R2 b = 0 ∧ projection36Phi18R3 b = 0 ∧
    projection36Phi18R4 b = 0 ∧ projection36Phi18R5 b = 0 := by
  rcases remainderCoeff_eighteen b with ⟨h0, h1, h2, h3, h4, h5⟩
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
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 0) (b 6) (b 9) (b 15) (b 18) (b 24) (b 27) (b 33) k0
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk0
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 1) (b 7) (b 10) (b 16) (b 19) (b 25) (b 28) (b 34) k1
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk1
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 2) (b 8) (b 11) (b 17) (b 20) (b 26) (b 29) (b 35) k2
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk2
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 3) (b 12) (b 15) (b 6) (b 21) (b 30) (b 33) (b 24) k3
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk3])
  constructor
  · exact signed_four_four_five_mul_eq_zero
      (b 4) (b 13) (b 16) (b 7) (b 22) (b 31) (b 34) (b 25) k4
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk4])
  · exact signed_four_four_five_mul_eq_zero
      (b 5) (b 14) (b 17) (b 8) (b 23) (b 32) (b 35) (b 26) k5
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk5])

/-- The same bound argument for the twelve order-36 coordinates. -/
theorem projection36_phi36_remainders_zero_of_mod_five_dvd
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hdiv : cyclotomic 36 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    projection36Phi36R0 b = 0 ∧ projection36Phi36R1 b = 0 ∧
    projection36Phi36R2 b = 0 ∧ projection36Phi36R3 b = 0 ∧
    projection36Phi36R4 b = 0 ∧ projection36Phi36R5 b = 0 ∧
    projection36Phi36R6 b = 0 ∧ projection36Phi36R7 b = 0 ∧
    projection36Phi36R8 b = 0 ∧ projection36Phi36R9 b = 0 ∧
    projection36Phi36R10 b = 0 ∧ projection36Phi36R11 b = 0 := by
  rcases remainderCoeff_thirtysix b with
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
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 0) (b 12) (b 18) (b 30) k0
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk0
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 1) (b 13) (b 19) (b 31) k1
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk1
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 2) (b 14) (b 20) (b 32) k2
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk2
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 3) (b 15) (b 21) (b 33) k3
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk3
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 4) (b 16) (b 22) (b 34) k4
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk4
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 5) (b 17) (b 23) (b 35) k5
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) hk5
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 6) (b 24) (b 30) (b 12) k6
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk6])
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 7) (b 25) (b 31) (b 13) k7
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk7])
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 8) (b 26) (b 32) (b 14) k8
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk8])
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 9) (b 27) (b 33) (b 15) k9
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk9])
  constructor
  · exact signed_two_two_five_mul_eq_zero (b 10) (b 28) (b 34) (b 16) k10
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk10])
  · exact signed_two_two_five_mul_eq_zero (b 11) (b 29) (b 35) (b 17) k11
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (by linarith only [hk11])

theorem cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero
    (b : Fin 36 → Int)
    (hz : projection36Phi9R0 b = 0 ∧ projection36Phi9R1 b = 0 ∧
      projection36Phi9R2 b = 0 ∧ projection36Phi9R3 b = 0 ∧
      projection36Phi9R4 b = 0 ∧ projection36Phi9R5 b = 0) :
    cyclotomic 9 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3, z4, z5⟩
  rcases remainderCoeff_nine b with ⟨h0, h1, h2, h3, h4, h5⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  norm_num at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3
  · exact h4.trans z4
  · exact h5.trans z5

theorem cyclotomic_eighteen_dvd_projection36Indicator_of_remainders_zero
    (b : Fin 36 → Int)
    (hz : projection36Phi18R0 b = 0 ∧ projection36Phi18R1 b = 0 ∧
      projection36Phi18R2 b = 0 ∧ projection36Phi18R3 b = 0 ∧
      projection36Phi18R4 b = 0 ∧ projection36Phi18R5 b = 0) :
    cyclotomic 18 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3, z4, z5⟩
  rcases remainderCoeff_eighteen b with ⟨h0, h1, h2, h3, h4, h5⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  norm_num at hj
  interval_cases j
  · exact h0.trans z0
  · exact h1.trans z1
  · exact h2.trans z2
  · exact h3.trans z3
  · exact h4.trans z4
  · exact h5.trans z5

theorem cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero
    (b : Fin 36 → Int)
    (hz : projection36Phi36R0 b = 0 ∧ projection36Phi36R1 b = 0 ∧
      projection36Phi36R2 b = 0 ∧ projection36Phi36R3 b = 0 ∧
      projection36Phi36R4 b = 0 ∧ projection36Phi36R5 b = 0 ∧
      projection36Phi36R6 b = 0 ∧ projection36Phi36R7 b = 0 ∧
      projection36Phi36R8 b = 0 ∧ projection36Phi36R9 b = 0 ∧
      projection36Phi36R10 b = 0 ∧ projection36Phi36R11 b = 0) :
    cyclotomic 36 Int ∣ projection36IndicatorMask b := by
  rcases hz with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11⟩
  rcases remainderCoeff_thirtysix b with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
  intro j hj
  norm_num at hj
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

#print axioms projection36_phi12_five_multipliers
#print axioms projection36_phi3_five_multipliers
#print axioms projection36_phi9_remainders_zero_of_mod_five_dvd
#print axioms projection36_phi18_remainders_zero_of_mod_five_dvd
#print axioms projection36_phi36_remainders_zero_of_mod_five_dvd
#print axioms cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero
#print axioms cyclotomic_eighteen_dvd_projection36Indicator_of_remainders_zero
#print axioms cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero

end Fuglede
