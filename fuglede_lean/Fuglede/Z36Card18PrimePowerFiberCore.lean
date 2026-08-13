import Fuglede.ProjectionFiberTiling
import Fuglede.PrimeCyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Two-primary projection fibres for eighteen points in `ZMod 36`

Projection to `ZMod 9` has a kernel of order four.  Thus every nonzero
difference within one fibre has exact order two or four.  This module also
records the two opposite two-point kernel patterns and the elementary
prime-square cardinality obstruction which rules out mixing the two orders.
-/

namespace Fuglede

open Polynomial

/-- A nonzero element in the kernel of `ZMod 36 → ZMod 9` has order two or
four. -/
theorem z36_frequencyOrder_two_or_four_of_cast9_eq :
    ∀ x y : ZMod 36,
      x ≠ y →
      (ZMod.cast x : ZMod 9) = ZMod.cast y →
      frequencyOrder 36 (x - y) = 2 ∨
        frequencyOrder 36 (x - y) = 4 := by
  intro x y hxy hcast
  have hcastZero : (ZMod.cast (x - y) : ZMod 9) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 9 ∣ 36), hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 9) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 9 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 9).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 4 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

private theorem z36_cyclotomic_two_not_dvd_cyclotomic_four :
    ¬ cyclotomic 2 ℤ ∣ cyclotomic 4 ℤ := by
  intro hdiv
  have hassoc : Associated (cyclotomic 2 ℤ) (cyclotomic 4 ℤ) :=
    Irreducible.associated_of_dvd
      (cyclotomic.irreducible (by norm_num : 0 < 2))
      (cyclotomic.irreducible (by norm_num : 0 < 4)) hdiv
  have hdegree : (cyclotomic 2 ℤ).natDegree =
      (cyclotomic 4 ℤ).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_cyclotomic, natDegree_cyclotomic] at hdegree
  have htotientTwo : Nat.totient 2 = 1 := Nat.totient_two
  have htotientFour : Nat.totient 4 = 2 := by
    rw [show 4 = 2 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num)]
    norm_num
  omega

private theorem z36_cyclotomic_two_mul_four_dvd_mask
    (X : Finset (ZMod 36))
    (htwo : cyclotomic 2 ℤ ∣ maskPolynomial 36 X)
    (hfour : cyclotomic 4 ℤ ∣ maskPolynomial 36 X) :
    cyclotomic 2 ℤ * cyclotomic 4 ℤ ∣ maskPolynomial 36 X := by
  obtain ⟨Q, hQ⟩ := hfour
  rw [hQ] at htwo ⊢
  rcases (cyclotomic.irreducible (by norm_num : 0 < 2)).prime.dvd_mul.mp htwo with
    hbad | hdivQ
  · exact False.elim (z36_cyclotomic_two_not_dvd_cyclotomic_four hbad)
  · obtain ⟨R, hR⟩ := hdivQ
    refine ⟨R, ?_⟩
    rw [hR]
    ring

/-- Simultaneous order-two and order-four zeros force a factor of four in
the cardinality of a subset of `ZMod 36`. -/
theorem z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
    (X : Finset (ZMod 36)) {d₂ d₄ : ZMod 36}
    (horder₂ : frequencyOrder 36 d₂ = 2)
    (horder₄ : frequencyOrder 36 d₄ = 4)
    (hzero₂ : CyclotomicZero 36 X d₂)
    (hzero₄ : CyclotomicZero 36 X d₄) :
    4 ∣ X.card := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have htwo : cyclotomic 2 ℤ ∣ maskPolynomial 36 X := by
    simpa [CyclotomicZero, horder₂] using hzero₂
  have hfour : cyclotomic 4 ℤ ∣ maskPolynomial 36 X := by
    simpa [CyclotomicZero, horder₄] using hzero₄
  obtain ⟨Q, hQ⟩ :=
    z36_cyclotomic_two_mul_four_dvd_mask X htwo hfour
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  have hevalFour : Polynomial.eval (1 : ℤ) (cyclotomic 4 ℤ) = 2 := by
    convert (eval_one_cyclotomic_prime_pow (R := ℤ) (p := 2) 1) using 1 <;>
      norm_num
  have hint : (4 : ℤ) ∣ (X.card : ℤ) := by
    refine ⟨Polynomial.eval 1 Q, ?_⟩
    simpa [eval_one_maskPolynomial, Polynomial.eval_mul, hevalFour] using heval
  exact_mod_cast hint

/-- Two kernel points whose nonzero differences have order four. -/
def z36Card18OrderFourComplement : Finset (ZMod 36) := {0, 9}

/-- The order-two subgroup of `ZMod 36`. -/
def z36Card18OrderTwoComplement : Finset (ZMod 36) := {0, 18}

@[simp]
theorem z36Card18OrderFourComplement_card :
    z36Card18OrderFourComplement.card = 2 := by
  decide

@[simp]
theorem z36Card18OrderTwoComplement_card :
    z36Card18OrderTwoComplement.card = 2 := by
  decide

theorem z36Card18OrderFourComplement_cast9_zero
    {b : ZMod 36} (hb : b ∈ z36Card18OrderFourComplement) :
    (ZMod.cast b : ZMod 9) = 0 := by
  simp only [z36Card18OrderFourComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

theorem z36Card18OrderTwoComplement_cast9_zero
    {b : ZMod 36} (hb : b ∈ z36Card18OrderTwoComplement) :
    (ZMod.cast b : ZMod 9) = 0 := by
  simp only [z36Card18OrderTwoComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

theorem z36Card18OrderFourComplement_difference_order
    {b b' : ZMod 36}
    (hb : b ∈ z36Card18OrderFourComplement)
    (hb' : b' ∈ z36Card18OrderFourComplement) (hne : b ≠ b') :
    frequencyOrder 36 (b - b') = 4 := by
  simp only [z36Card18OrderFourComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl <;>
    rcases hb' with rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

theorem z36Card18OrderTwoComplement_difference_order
    {b b' : ZMod 36}
    (hb : b ∈ z36Card18OrderTwoComplement)
    (hb' : b' ∈ z36Card18OrderTwoComplement) (hne : b ≠ b') :
    frequencyOrder 36 (b - b') = 2 := by
  simp only [z36Card18OrderTwoComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl <;>
    rcases hb' with rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

#print axioms z36_frequencyOrder_two_or_four_of_cast9_eq
#print axioms z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
#print axioms z36Card18OrderFourComplement_difference_order
#print axioms z36Card18OrderTwoComplement_difference_order

end Fuglede
