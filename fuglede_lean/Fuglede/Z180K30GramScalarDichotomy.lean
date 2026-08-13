import Mathlib.Tactic

/-!
# Scalar core of the K30 Gram dichotomy

This module contains only the finite real and natural-number arithmetic used
after a simultaneous eigenbasis has been supplied.  It does not assert the
existence of that eigenbasis or any Fourier-block identity.
-/

namespace Fuglede

open scoped BigOperators

def Z180K30GramNormalScalar (lambda : Fin 5 → ℝ) : Prop :=
  ∀ r, lambda r = 6

def Z180K30GramSpikeAt (lambda : Fin 5 → ℝ) (r : Fin 5) : Prop :=
  lambda r = 30 ∧ ∀ s, s ≠ r → lambda s = 0

def Z180K30GramSpikeScalar (lambda : Fin 5 → ℝ) : Prop :=
  ∃ r, Z180K30GramSpikeAt lambda r

private theorem finFive_exists_ne_and_ne (i j : Fin 5) :
    ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Five real numbers with sum thirty and one common off-diagonal product
are either all six, or one is thirty and the other four are zero. -/
theorem z180K30_five_scalar_gram_dichotomy
    (lambda : Fin 5 → ℝ)
    (hsum : (∑ r, lambda r) = 30)
    (hcross : ∃ q : ℝ,
      ∀ r s, r ≠ s → lambda r * lambda s = q) :
    Z180K30GramNormalScalar lambda ∨ Z180K30GramSpikeScalar lambda := by
  rcases hcross with ⟨q, hq⟩
  by_cases hqzero : q = 0
  · have hexists : ∃ r, lambda r ≠ 0 := by
      by_contra hallzero
      push_neg at hallzero
      have hzero : (∑ r, lambda r) = 0 := by simp [hallzero]
      linarith
    rcases hexists with ⟨owner, howner⟩
    right
    refine ⟨owner, ?_, ?_⟩
    · have hsumSingle : (∑ r, lambda r) = lambda owner := by
        rw [Fintype.sum_eq_single owner]
        intro s hs
        have hproduct := hq owner s hs.symm
        rw [hqzero] at hproduct
        exact (mul_eq_zero.mp hproduct).resolve_left howner
      linarith
    · intro s hs
      have hproduct := hq owner s hs.symm
      rw [hqzero] at hproduct
      exact (mul_eq_zero.mp hproduct).resolve_left howner
  · left
    have hnonzero : ∀ i, lambda i ≠ 0 := by
      intro i hi
      obtain ⟨j, hji, _⟩ := finFive_exists_ne_and_ne i i
      have hproduct := hq i j hji.symm
      rw [hi, zero_mul] at hproduct
      exact hqzero hproduct.symm
    have hequal : ∀ i j, lambda i = lambda j := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := finFive_exists_ne_and_ne i j
      have hik := hq i k hki.symm
      have hjk := hq j k hkj.symm
      exact mul_right_cancel₀ (hnonzero k) (hik.trans hjk.symm)
    intro i
    have hsumConst : (∑ j, lambda j) = (∑ _j : Fin 5, lambda i) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hequal j i
    have hfive : (∑ _j : Fin 5, lambda i) = 5 * lambda i := by
      norm_num
    linarith

/-- The six-dimensional trace equations have exactly the normal and the
rank-two multiplicity solutions. -/
theorem z180K30_trace_multiplicity_dichotomy
    (uniform : ℕ) (spike : Fin 5 → ℕ)
    (htrace : ∀ r, 6 * uniform + 30 * spike r = 36) :
    (uniform = 6 ∧ ∀ r, spike r = 0) ∨
      (uniform = 1 ∧ ∀ r, spike r = 1) := by
  have hzero := htrace (0 : Fin 5)
  have huniform : uniform = 6 ∨ uniform = 1 := by omega
  rcases huniform with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    intro r
    have hr := htrace r
    omega
  · right
    refine ⟨rfl, ?_⟩
    intro r
    have hr := htrace r
    omega

#print axioms z180K30_five_scalar_gram_dichotomy
#print axioms z180K30_trace_multiplicity_dichotomy

end Fuglede
