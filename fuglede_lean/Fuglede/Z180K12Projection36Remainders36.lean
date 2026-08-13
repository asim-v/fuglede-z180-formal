import Fuglede.Z180K12Projection36Remainders18
import Mathlib.Tactic

/-!
# Concrete `Phi_36` remainders for the 36-coordinate projection
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The sparse integral form of the thirty-sixth cyclotomic polynomial. -/
theorem cyclotomic_thirtysix_eq_int :
    cyclotomic 36 Int = X ^ 12 - X ^ 6 + 1 := by
  rw [show 36 = 18 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num)]
  rw [cyclotomic_eighteen_eq_int]
  simp
  ring

/-- All twelve integral remainder coefficients modulo `Phi_36`. -/
theorem projection36_phi36_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 36 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    b 0 - b 12 - b 18 + b 30 = 0 ∧
    b 1 - b 13 - b 19 + b 31 = 0 ∧
    b 2 - b 14 - b 20 + b 32 = 0 ∧
    b 3 - b 15 - b 21 + b 33 = 0 ∧
    b 4 - b 16 - b 22 + b 34 = 0 ∧
    b 5 - b 17 - b 23 + b 35 = 0 ∧
    b 6 + b 12 - b 24 - b 30 = 0 ∧
    b 7 + b 13 - b 25 - b 31 = 0 ∧
    b 8 + b 14 - b 26 - b 32 = 0 ∧
    b 9 + b 15 - b 27 - b 33 = 0 ∧
    b 10 + b 16 - b 28 - b 34 = 0 ∧
    b 11 + b 17 - b 29 - b 35 = 0 := by
  let e0 := b 0 - b 12 - b 18 + b 30
  let e1 := b 1 - b 13 - b 19 + b 31
  let e2 := b 2 - b 14 - b 20 + b 32
  let e3 := b 3 - b 15 - b 21 + b 33
  let e4 := b 4 - b 16 - b 22 + b 34
  let e5 := b 5 - b 17 - b 23 + b 35
  let e6 := b 6 + b 12 - b 24 - b 30
  let e7 := b 7 + b 13 - b 25 - b 31
  let e8 := b 8 + b 14 - b 26 - b 32
  let e9 := b 9 + b 15 - b 27 - b 33
  let e10 := b 10 + b 16 - b 28 - b 34
  let e11 := b 11 + b 17 - b 29 - b 35
  let q0 := b 12 + b 18 - b 30
  let q1 := b 13 + b 19 - b 31
  let q2 := b 14 + b 20 - b 32
  let q3 := b 15 + b 21 - b 33
  let q4 := b 16 + b 22 - b 34
  let q5 := b 17 + b 23 - b 35
  let q6 := b 18 + b 24
  let q7 := b 19 + b 25
  let q8 := b 20 + b 26
  let q9 := b 21 + b 27
  let q10 := b 22 + b 28
  let q11 := b 23 + b 29
  let q12 := b 24 + b 30
  let q13 := b 25 + b 31
  let q14 := b 26 + b 32
  let q15 := b 27 + b 33
  let q16 := b 28 + b 34
  let q17 := b 29 + b 35
  let q18 := b 30
  let q19 := b 31
  let q20 := b 32
  let q21 := b 33
  let q22 := b 34
  let q23 := b 35
  let Q : Polynomial Int :=
      monomial 0 q0 +
      monomial 1 q1 +
      monomial 2 q2 +
      monomial 3 q3 +
      monomial 4 q4 +
      monomial 5 q5 +
      monomial 6 q6 +
      monomial 7 q7 +
      monomial 8 q8 +
      monomial 9 q9 +
      monomial 10 q10 +
      monomial 11 q11 +
      monomial 12 q12 +
      monomial 13 q13 +
      monomial 14 q14 +
      monomial 15 q15 +
      monomial 16 q16 +
      monomial 17 q17 +
      monomial 18 q18 +
      monomial 19 q19 +
      monomial 20 q20 +
      monomial 21 q21 +
      monomial 22 q22 +
      monomial 23 q23
  let R : Polynomial Int :=
      monomial 0 e0 +
      monomial 1 e1 +
      monomial 2 e2 +
      monomial 3 e3 +
      monomial 4 e4 +
      monomial 5 e5 +
      monomial 6 e6 +
      monomial 7 e7 +
      monomial 8 e8 +
      monomial 9 e9 +
      monomial 10 e10 +
      monomial 11 e11
  let bn : Nat → Int := fun n ↦
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [Nat.mod_eq_of_lt i.isLt]
  have hbn0 : bn 0 = b 0 := by
    simpa using hbn (0 : Fin 36)
  have hbn1 : bn 1 = b 1 := by
    simpa using hbn (1 : Fin 36)
  have hbn2 : bn 2 = b 2 := by
    simpa using hbn (2 : Fin 36)
  have hbn3 : bn 3 = b 3 := by
    simpa using hbn (3 : Fin 36)
  have hbn4 : bn 4 = b 4 := by
    simpa using hbn (4 : Fin 36)
  have hbn5 : bn 5 = b 5 := by
    simpa using hbn (5 : Fin 36)
  have hbn6 : bn 6 = b 6 := by
    simpa using hbn (6 : Fin 36)
  have hbn7 : bn 7 = b 7 := by
    simpa using hbn (7 : Fin 36)
  have hbn8 : bn 8 = b 8 := by
    simpa using hbn (8 : Fin 36)
  have hbn9 : bn 9 = b 9 := by
    simpa using hbn (9 : Fin 36)
  have hbn10 : bn 10 = b 10 := by
    simpa using hbn (10 : Fin 36)
  have hbn11 : bn 11 = b 11 := by
    simpa using hbn (11 : Fin 36)
  have hbn12 : bn 12 = b 12 := by
    simpa using hbn (12 : Fin 36)
  have hbn13 : bn 13 = b 13 := by
    simpa using hbn (13 : Fin 36)
  have hbn14 : bn 14 = b 14 := by
    simpa using hbn (14 : Fin 36)
  have hbn15 : bn 15 = b 15 := by
    simpa using hbn (15 : Fin 36)
  have hbn16 : bn 16 = b 16 := by
    simpa using hbn (16 : Fin 36)
  have hbn17 : bn 17 = b 17 := by
    simpa using hbn (17 : Fin 36)
  have hbn18 : bn 18 = b 18 := by
    simpa using hbn (18 : Fin 36)
  have hbn19 : bn 19 = b 19 := by
    simpa using hbn (19 : Fin 36)
  have hbn20 : bn 20 = b 20 := by
    simpa using hbn (20 : Fin 36)
  have hbn21 : bn 21 = b 21 := by
    simpa using hbn (21 : Fin 36)
  have hbn22 : bn 22 = b 22 := by
    simpa using hbn (22 : Fin 36)
  have hbn23 : bn 23 = b 23 := by
    simpa using hbn (23 : Fin 36)
  have hbn24 : bn 24 = b 24 := by
    simpa using hbn (24 : Fin 36)
  have hbn25 : bn 25 = b 25 := by
    simpa using hbn (25 : Fin 36)
  have hbn26 : bn 26 = b 26 := by
    simpa using hbn (26 : Fin 36)
  have hbn27 : bn 27 = b 27 := by
    simpa using hbn (27 : Fin 36)
  have hbn28 : bn 28 = b 28 := by
    simpa using hbn (28 : Fin 36)
  have hbn29 : bn 29 = b 29 := by
    simpa using hbn (29 : Fin 36)
  have hbn30 : bn 30 = b 30 := by
    simpa using hbn (30 : Fin 36)
  have hbn31 : bn 31 = b 31 := by
    simpa using hbn (31 : Fin 36)
  have hbn32 : bn 32 = b 32 := by
    simpa using hbn (32 : Fin 36)
  have hbn33 : bn 33 = b 33 := by
    simpa using hbn (33 : Fin 36)
  have hbn34 : bn 34 = b 34 := by
    simpa using hbn (34 : Fin 36)
  have hbn35 : bn 35 = b 35 := by
    simpa using hbn (35 : Fin 36)
  have hsum :
      (∑ i : Fin 36, monomial i.val (b i)) =
        ∑ i : Fin 36, monomial i.val (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  have hidentity :
      (∑ i : Fin 36, monomial i.val (b i)) -
          cyclotomic 36 Int * Q = R := by
    rw [cyclotomic_thirtysix_eq_int]
    dsimp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, Q, R]
    rw [hsum]
    rw [Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial n (bn n)) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    simp only [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    ring
  have hRdiv : cyclotomic 36 Int ∣ R := by
    rw [← hidentity]
    exact dvd_sub hdiv (dvd_mul_right _ _)
  have hRdegree : R.degree < (12 : Nat) := by
    apply (degree_lt_iff_coeff_zero R 12).2
    intro m hm
    have hmNat : 12 ≤ m := by exact_mod_cast hm
    have h0 : (0 : Nat) ≠ m := by omega
    have h1 : (1 : Nat) ≠ m := by omega
    have h2 : (2 : Nat) ≠ m := by omega
    have h3 : (3 : Nat) ≠ m := by omega
    have h4 : (4 : Nat) ≠ m := by omega
    have h5 : (5 : Nat) ≠ m := by omega
    have h6 : (6 : Nat) ≠ m := by omega
    have h7 : (7 : Nat) ≠ m := by omega
    have h8 : (8 : Nat) ≠ m := by omega
    have h9 : (9 : Nat) ≠ m := by omega
    have h10 : (10 : Nat) ≠ m := by omega
    have h11 : (11 : Nat) ≠ m := by omega
    simp only [R, coeff_add, coeff_monomial, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10, if_neg h11, add_zero]
  have hRzero : R = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hRdiv
    rw [degree_cyclotomic, show Nat.totient 36 = 12 by decide]
    exact hRdegree
  have h0 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hRzero
  have h1 := congrArg (fun P : Polynomial Int ↦ P.coeff 1) hRzero
  have h2 := congrArg (fun P : Polynomial Int ↦ P.coeff 2) hRzero
  have h3 := congrArg (fun P : Polynomial Int ↦ P.coeff 3) hRzero
  have h4 := congrArg (fun P : Polynomial Int ↦ P.coeff 4) hRzero
  have h5 := congrArg (fun P : Polynomial Int ↦ P.coeff 5) hRzero
  have h6 := congrArg (fun P : Polynomial Int ↦ P.coeff 6) hRzero
  have h7 := congrArg (fun P : Polynomial Int ↦ P.coeff 7) hRzero
  have h8 := congrArg (fun P : Polynomial Int ↦ P.coeff 8) hRzero
  have h9 := congrArg (fun P : Polynomial Int ↦ P.coeff 9) hRzero
  have h10 := congrArg (fun P : Polynomial Int ↦ P.coeff 10) hRzero
  have h11 := congrArg (fun P : Polynomial Int ↦ P.coeff 11) hRzero
  simp only [R, coeff_add, coeff_monomial] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  dsimp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

#print axioms cyclotomic_thirtysix_eq_int
#print axioms projection36_phi36_remainders

end Fuglede
