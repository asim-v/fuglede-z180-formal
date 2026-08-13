import Fuglede.ExactOrderDistribution
import Fuglede.FourierTiling
import Fuglede.Z180K12Projection36Remainders36
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Five fixed Fourier covers for six-point subsets of `ZMod 36`

The five order sets below are the minimal cyclotomic-zero patterns found by
the exact `Z/36Z`, cardinality-six classification.  Each has a fixed
six-point complement whose mask supplies all remaining nontrivial orders.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Divisibility of the mask by the cyclotomic polynomial of a given order. -/
def Z36ZeroAtOrder (A : Finset (ZMod 36)) (m : Nat) : Prop :=
  cyclotomic m Int ∣ maskPolynomial 36 A

def z36Card6Complement236 : Finset (ZMod 36) :=
  {0, 6, 12, 18, 24, 30}

def z36Card6Complement2918 : Finset (ZMod 36) :=
  {0, 2, 4, 18, 20, 22}

def z36Card6Complement3412 : Finset (ZMod 36) :=
  {0, 3, 12, 15, 24, 27}

/-- Complement for set-side zeros at orders `4,9,12,36`. -/
def z36Card6Complement491236 : Finset (ZMod 36) :=
  {0, 1, 2, 9, 10, 11}

/-- Complement for set-side zeros at orders `4,9,18,36`. -/
def z36Card6Complement491836 : Finset (ZMod 36) :=
  {0, 1, 4, 5, 8, 9}

@[simp] private theorem z36_val_1 : (1 : ZMod 36).val = 1 := by decide
@[simp] private theorem z36_val_2 : (2 : ZMod 36).val = 2 := by decide
@[simp] private theorem z36_val_3 : (3 : ZMod 36).val = 3 := by decide
@[simp] private theorem z36_val_4 : (4 : ZMod 36).val = 4 := by decide
@[simp] private theorem z36_val_5 : (5 : ZMod 36).val = 5 := by decide
@[simp] private theorem z36_val_6 : (6 : ZMod 36).val = 6 := by decide
@[simp] private theorem z36_val_8 : (8 : ZMod 36).val = 8 := by decide
@[simp] private theorem z36_val_9 : (9 : ZMod 36).val = 9 := by decide
@[simp] private theorem z36_val_10 : (10 : ZMod 36).val = 10 := by decide
@[simp] private theorem z36_val_11 : (11 : ZMod 36).val = 11 := by decide
@[simp] private theorem z36_val_12 : (12 : ZMod 36).val = 12 := by decide
@[simp] private theorem z36_val_15 : (15 : ZMod 36).val = 15 := by decide
@[simp] private theorem z36_val_18 : (18 : ZMod 36).val = 18 := by decide
@[simp] private theorem z36_val_20 : (20 : ZMod 36).val = 20 := by decide
@[simp] private theorem z36_val_22 : (22 : ZMod 36).val = 22 := by decide
@[simp] private theorem z36_val_24 : (24 : ZMod 36).val = 24 := by decide
@[simp] private theorem z36_val_27 : (27 : ZMod 36).val = 27 := by decide
@[simp] private theorem z36_val_30 : (30 : ZMod 36).val = 30 := by decide

private theorem cyclotomic_four_int :
    cyclotomic 4 Int = X ^ 2 + 1 := by
  rw [show 4 = 2 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ]
  ring

private theorem cyclotomic_nine_int :
    cyclotomic 9 Int = X ^ 6 + X ^ 3 + 1 := by
  rw [show 9 = 3 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum (by norm_num : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]
  ring

private theorem cyclotomic_twelve_int :
    cyclotomic 12 Int = X ^ 4 - X ^ 2 + 1 := by
  rw [show 12 = 6 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num)]
  rw [cyclotomic_six]
  simp
  ring

private theorem z36_mask_complement236_factorization :
    maskPolynomial 36 z36Card6Complement236 =
      cyclotomic 4 Int * cyclotomic 9 Int * cyclotomic 12 Int *
        cyclotomic 18 Int * cyclotomic 36 Int := by
  rw [cyclotomic_four_int, cyclotomic_nine_int, cyclotomic_twelve_int,
    cyclotomic_eighteen_eq_int, cyclotomic_thirtysix_eq_int]
  simp +decide [maskPolynomial, z36Card6Complement236]
  ring

private theorem z36_mask_complement2918_factorization :
    maskPolynomial 36 z36Card6Complement2918 =
      cyclotomic 3 Int * cyclotomic 4 Int * cyclotomic 6 Int *
        cyclotomic 12 Int * cyclotomic 36 Int := by
  rw [cyclotomic_three, cyclotomic_four_int, cyclotomic_six,
    cyclotomic_twelve_int, cyclotomic_thirtysix_eq_int]
  simp +decide [maskPolynomial, z36Card6Complement2918]
  ring

private theorem z36_mask_complement3412_factorization :
    maskPolynomial 36 z36Card6Complement3412 =
      cyclotomic 2 Int * cyclotomic 6 Int * cyclotomic 9 Int *
        cyclotomic 18 Int * cyclotomic 36 Int := by
  rw [cyclotomic_two, cyclotomic_six, cyclotomic_nine_int,
    cyclotomic_eighteen_eq_int, cyclotomic_thirtysix_eq_int]
  simp +decide [maskPolynomial, z36Card6Complement3412]
  ring

private theorem z36_mask_complement491236_factorization :
    maskPolynomial 36 z36Card6Complement491236 =
      cyclotomic 2 Int * cyclotomic 3 Int * cyclotomic 6 Int *
        cyclotomic 18 Int := by
  rw [cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic_eighteen_eq_int]
  simp +decide [maskPolynomial, z36Card6Complement491236]
  ring

private theorem z36_mask_complement491836_factorization :
    maskPolynomial 36 z36Card6Complement491836 =
      cyclotomic 2 Int * cyclotomic 3 Int * cyclotomic 6 Int *
        cyclotomic 12 Int := by
  rw [cyclotomic_two, cyclotomic_three, cyclotomic_six,
    cyclotomic_twelve_int]
  simp +decide [maskPolynomial, z36Card6Complement491836]
  ring

private theorem z36_frequencyOrder_cases {d : ZMod 36} (hd : d ≠ 0) :
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

private theorem zero_of_order
    {A : Finset (ZMod 36)} {d : ZMod 36} {m : Nat}
    (hm : frequencyOrder 36 d = m) (h : Z36ZeroAtOrder A m) :
    CyclotomicZero 36 A d := by
  simpa [CyclotomicZero, Z36ZeroAtOrder, hm] using h

private theorem all_dvd_product5 (a b c d e : Polynomial Int) :
    a ∣ a * b * c * d * e ∧ b ∣ a * b * c * d * e ∧
    c ∣ a * b * c * d * e ∧ d ∣ a * b * c * d * e ∧
    e ∣ a * b * c * d * e := by
  constructor
  · exact ⟨b * c * d * e, by ring⟩
  constructor
  · exact ⟨a * c * d * e, by ring⟩
  constructor
  · exact ⟨a * b * d * e, by ring⟩
  constructor
  · exact ⟨a * b * c * e, by ring⟩
  · exact ⟨a * b * c * d, by ring⟩

private theorem all_dvd_product4 (a b c d : Polynomial Int) :
    a ∣ a * b * c * d ∧ b ∣ a * b * c * d ∧
    c ∣ a * b * c * d ∧ d ∣ a * b * c * d := by
  constructor
  · exact ⟨b * c * d, by ring⟩
  constructor
  · exact ⟨a * c * d, by ring⟩
  constructor
  · exact ⟨a * b * d, by ring⟩
  · exact ⟨a * b * c, by ring⟩

private theorem complement236_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 4 ∨ frequencyOrder 36 d = 9 ∨
      frequencyOrder 36 d = 12 ∨ frequencyOrder 36 d = 18 ∨
      frequencyOrder 36 d = 36) :
    CyclotomicZero 36 z36Card6Complement236 d := by
  rw [CyclotomicZero, z36_mask_complement236_factorization]
  rcases horder with h | h | h | h | h
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.2

private theorem complement2918_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 3 ∨ frequencyOrder 36 d = 4 ∨
      frequencyOrder 36 d = 6 ∨ frequencyOrder 36 d = 12 ∨
      frequencyOrder 36 d = 36) :
    CyclotomicZero 36 z36Card6Complement2918 d := by
  rw [CyclotomicZero, z36_mask_complement2918_factorization]
  rcases horder with h | h | h | h | h
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.2

private theorem complement3412_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 6 ∨
      frequencyOrder 36 d = 9 ∨ frequencyOrder 36 d = 18 ∨
      frequencyOrder 36 d = 36) :
    CyclotomicZero 36 z36Card6Complement3412 d := by
  rw [CyclotomicZero, z36_mask_complement3412_factorization]
  rcases horder with h | h | h | h | h
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.1
  · rw [h]; exact (all_dvd_product5 _ _ _ _ _).2.2.2.2

private theorem complement491236_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 3 ∨
      frequencyOrder 36 d = 6 ∨ frequencyOrder 36 d = 18) :
    CyclotomicZero 36 z36Card6Complement491236 d := by
  rw [CyclotomicZero, z36_mask_complement491236_factorization]
  rcases horder with h | h | h | h
  · rw [h]; exact (all_dvd_product4 _ _ _ _).1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.2.2

private theorem complement491836_zero
    {d : ZMod 36}
    (horder : frequencyOrder 36 d = 2 ∨ frequencyOrder 36 d = 3 ∨
      frequencyOrder 36 d = 6 ∨ frequencyOrder 36 d = 12) :
    CyclotomicZero 36 z36Card6Complement491836 d := by
  rw [CyclotomicZero, z36_mask_complement491836_factorization]
  rcases horder with h | h | h | h
  · rw [h]; exact (all_dvd_product4 _ _ _ _).1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.2.1
  · rw [h]; exact (all_dvd_product4 _ _ _ _).2.2.2

theorem z36_card6_tiles_of_zeros_2_3_6
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h2 : Z36ZeroAtOrder A 2) (h3 : Z36ZeroAtOrder A 3)
    (h6 : Z36ZeroAtOrder A 6) :
    Tiles A z36Card6Complement236 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases hd with h | h | h | h | h | h | h | h
    · exact Or.inl (zero_of_order h h2)
    · exact Or.inl (zero_of_order h h3)
    · exact Or.inr (complement236_zero (Or.inl h))
    · exact Or.inl (zero_of_order h h6)
    · exact Or.inr (complement236_zero (Or.inr (Or.inl h)))
    · exact Or.inr (complement236_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (complement236_zero (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (complement236_zero (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem z36_card6_tiles_of_zeros_2_9_18
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h2 : Z36ZeroAtOrder A 2) (h9 : Z36ZeroAtOrder A 9)
    (h18 : Z36ZeroAtOrder A 18) :
    Tiles A z36Card6Complement2918 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases hd with h | h | h | h | h | h | h | h
    · exact Or.inl (zero_of_order h h2)
    · exact Or.inr (complement2918_zero (Or.inl h))
    · exact Or.inr (complement2918_zero (Or.inr (Or.inl h)))
    · exact Or.inr (complement2918_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (zero_of_order h h9)
    · exact Or.inr (complement2918_zero (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inl (zero_of_order h h18)
    · exact Or.inr (complement2918_zero (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem z36_card6_tiles_of_zeros_3_4_12
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h3 : Z36ZeroAtOrder A 3) (h4 : Z36ZeroAtOrder A 4)
    (h12 : Z36ZeroAtOrder A 12) :
    Tiles A z36Card6Complement3412 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases hd with h | h | h | h | h | h | h | h
    · exact Or.inr (complement3412_zero (Or.inl h))
    · exact Or.inl (zero_of_order h h3)
    · exact Or.inl (zero_of_order h h4)
    · exact Or.inr (complement3412_zero (Or.inr (Or.inl h)))
    · exact Or.inr (complement3412_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (zero_of_order h h12)
    · exact Or.inr (complement3412_zero (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (complement3412_zero (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem z36_card6_tiles_of_zeros_4_9_12_36
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h4 : Z36ZeroAtOrder A 4) (h9 : Z36ZeroAtOrder A 9)
    (h12 : Z36ZeroAtOrder A 12) (h36 : Z36ZeroAtOrder A 36) :
    Tiles A z36Card6Complement491236 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases hd with h | h | h | h | h | h | h | h
    · exact Or.inr (complement491236_zero (Or.inl h))
    · exact Or.inr (complement491236_zero (Or.inr (Or.inl h)))
    · exact Or.inl (zero_of_order h h4)
    · exact Or.inr (complement491236_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (zero_of_order h h9)
    · exact Or.inl (zero_of_order h h12)
    · exact Or.inr (complement491236_zero (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (zero_of_order h h36)

theorem z36_card6_tiles_of_zeros_4_9_18_36
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h4 : Z36ZeroAtOrder A 4) (h9 : Z36ZeroAtOrder A 9)
    (h18 : Z36ZeroAtOrder A 18) (h36 : Z36ZeroAtOrder A 36) :
    Tiles A z36Card6Complement491836 := by
  apply tiles_of_cyclotomic_zero_cover
  · rw [hcard]
    decide
  · intro d hd
    rcases z36_frequencyOrder_cases hd with h | h | h | h | h | h | h | h
    · exact Or.inr (complement491836_zero (Or.inl h))
    · exact Or.inr (complement491836_zero (Or.inr (Or.inl h)))
    · exact Or.inl (zero_of_order h h4)
    · exact Or.inr (complement491836_zero (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (zero_of_order h h9)
    · exact Or.inr (complement491836_zero (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (zero_of_order h h18)
    · exact Or.inl (zero_of_order h h36)

#print axioms z36_card6_tiles_of_zeros_2_3_6
#print axioms z36_card6_tiles_of_zeros_2_9_18
#print axioms z36_card6_tiles_of_zeros_3_4_12
#print axioms z36_card6_tiles_of_zeros_4_9_12_36
#print axioms z36_card6_tiles_of_zeros_4_9_18_36

end Fuglede
