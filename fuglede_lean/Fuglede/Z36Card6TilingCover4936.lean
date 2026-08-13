import Fuglede.Z36Card6TilingCovers
import Mathlib.Tactic

/-!
# A common fixed cover for the `4,9,36` branch in `ZMod 36`

The exact six-point census produces a branch in which the set mask vanishes
at orders `4`, `9`, and `36`.  The fixed set below supplies the complementary
orders `2`, `3`, `6`, `12`, and `18`, so the Fourier-zero cover theorem gives
a tiling without choosing between the order-`12` and order-`18` forcing
subbranches.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Fixed six-point complement for set-side zeros at orders `4,9,36`. -/
def z36Card6Complement4936 : Finset (ZMod 36) :=
  {0, 1, 5, 9, 28, 32}

@[simp] private theorem z36_c4936_val_1 : (1 : ZMod 36).val = 1 := by decide
@[simp] private theorem z36_c4936_val_5 : (5 : ZMod 36).val = 5 := by decide
@[simp] private theorem z36_c4936_val_9 : (9 : ZMod 36).val = 9 := by decide
@[simp] private theorem z36_c4936_val_28 : (28 : ZMod 36).val = 28 := by decide
@[simp] private theorem z36_c4936_val_32 : (32 : ZMod 36).val = 32 := by decide

private theorem cyclotomic_twelve_int_4936 :
    cyclotomic 12 Int = X ^ 4 - X ^ 2 + 1 := by
  rw [show 12 = 6 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num)]
  rw [cyclotomic_six]
  simp
  ring

/-- The quotient left after extracting the five complementary cyclotomic
factors from the concrete mask. -/
private noncomputable def z36Card6Complement4936Quotient : Polynomial Int :=
  X ^ 17 - X ^ 16 + X ^ 15 - X ^ 9 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 + 1

private theorem z36_mask_complement4936_factorization :
    maskPolynomial 36 z36Card6Complement4936 =
      cyclotomic 2 Int * cyclotomic 3 Int * cyclotomic 6 Int *
        cyclotomic 12 Int * cyclotomic 18 Int *
          z36Card6Complement4936Quotient := by
  rw [cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic_twelve_int_4936, cyclotomic_eighteen_eq_int]
  simp +decide [maskPolynomial, z36Card6Complement4936,
    z36Card6Complement4936Quotient]
  ring

private theorem z36_frequencyOrder_cases_4936
    {d : ZMod 36} (hd : d ≠ 0) :
    frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 3 ∨
    frequencyOrder 36 d = 4 ∨ frequencyOrder 36 d = 6 ∨
    frequencyOrder 36 d = 9 ∨ frequencyOrder 36 d = 12 ∨
    frequencyOrder 36 d = 18 ∨ frequencyOrder 36 d = 36 := by
  have hgt : 1 < frequencyOrder 36 d :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hd
  have hdvd : frequencyOrder 36 d ∣ 36 := frequencyOrder_dvd_modulus d
  have hmem : frequencyOrder 36 d ∈ (36 : Nat).divisors :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivisors : (36 : Nat).divisors = {1, 2, 3, 4, 6, 9, 12, 18, 36} := by
    decide
  rw [hdivisors] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

private theorem z36_zero_of_order_4936
    {A : Finset (ZMod 36)} {d : ZMod 36} {m : Nat}
    (hm : frequencyOrder 36 d = m) (h : Z36ZeroAtOrder A m) :
    CyclotomicZero 36 A d := by
  simpa [CyclotomicZero, Z36ZeroAtOrder, hm] using h

private theorem all_dvd_product5_mul_4936
    (a b c d e q : Polynomial Int) :
    a ∣ a * b * c * d * e * q ∧ b ∣ a * b * c * d * e * q ∧
    c ∣ a * b * c * d * e * q ∧ d ∣ a * b * c * d * e * q ∧
    e ∣ a * b * c * d * e * q := by
  constructor
  · exact ⟨b * c * d * e * q, by ring⟩
  constructor
  · exact ⟨a * c * d * e * q, by ring⟩
  constructor
  · exact ⟨a * b * d * e * q, by ring⟩
  constructor
  · exact ⟨a * b * c * e * q, by ring⟩
  · exact ⟨a * b * c * d * q, by ring⟩

private theorem z36_complement4936_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 3 ∨
      frequencyOrder 36 d = 6 ∨ frequencyOrder 36 d = 12 ∨
      frequencyOrder 36 d = 18) :
    CyclotomicZero 36 z36Card6Complement4936 d := by
  rw [CyclotomicZero, z36_mask_complement4936_factorization]
  rcases horder with h | h | h | h | h
  · rw [h]; exact (all_dvd_product5_mul_4936 _ _ _ _ _ _).1
  · rw [h]; exact (all_dvd_product5_mul_4936 _ _ _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product5_mul_4936 _ _ _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product5_mul_4936 _ _ _ _ _ _).2.2.2.1
  · rw [h]; exact (all_dvd_product5_mul_4936 _ _ _ _ _ _).2.2.2.2

/-- A six-point set with mask zeros at orders `4`, `9`, and `36` tiles with
the single fixed complement `z36Card6Complement4936`. -/
theorem z36_card6_tiles_of_zeros_4_9_36
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h4 : Z36ZeroAtOrder A 4) (h9 : Z36ZeroAtOrder A 9)
    (h36 : Z36ZeroAtOrder A 36) :
    Tiles A z36Card6Complement4936 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases_4936 hd with h | h | h | h | h | h | h | h
    · exact Or.inr (z36_complement4936_zero (Or.inl h))
    · exact Or.inr (z36_complement4936_zero (Or.inr (Or.inl h)))
    · exact Or.inl (z36_zero_of_order_4936 h h4)
    · exact Or.inr (z36_complement4936_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (z36_zero_of_order_4936 h h9)
    · exact Or.inr
        (z36_complement4936_zero (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr
        (z36_complement4936_zero
          (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact Or.inl (z36_zero_of_order_4936 h h36)

#print axioms z36_card6_tiles_of_zeros_4_9_36

end Fuglede
