import Fuglede.Z180K12Projection36Remainders
import Mathlib.Tactic

/-!
# Concrete `Phi_18` remainders for the 36-coordinate projection
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem cyclotomic_nine_eq18 :
    cyclotomic 9 Int = X ^ 6 + X ^ 3 + 1 := by
  rw [show 9 = 3 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum (by norm_num : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]
  ring

/-- The sparse integral form of the eighteenth cyclotomic polynomial. -/
theorem cyclotomic_eighteen_eq_int :
    cyclotomic 18 Int = X ^ 6 - X ^ 3 + 1 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 9 Int)
  rw [show 18 = 9 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (by norm_num)]
  rw [cyclotomic_nine_eq18]
  simp
  ring

/-- All six integral remainder coefficients modulo `Phi_18`. -/
theorem projection36_phi18_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 18 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33 = 0 ∧
    b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34 = 0 ∧
    b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35 = 0 ∧
    b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33 = 0 ∧
    b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34 = 0 ∧
    b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35 = 0 := by
  let s0 := b 0 + b 18
  let s1 := b 1 + b 19
  let s2 := b 2 + b 20
  let s3 := b 3 + b 21
  let s4 := b 4 + b 22
  let s5 := b 5 + b 23
  let s6 := b 6 + b 24
  let s7 := b 7 + b 25
  let s8 := b 8 + b 26
  let s9 := b 9 + b 27
  let s10 := b 10 + b 28
  let s11 := b 11 + b 29
  let s12 := b 12 + b 30
  let s13 := b 13 + b 31
  let s14 := b 14 + b 32
  let s15 := b 15 + b 33
  let s16 := b 16 + b 34
  let s17 := b 17 + b 35
  let e0 := b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33
  let e1 := b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34
  let e2 := b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35
  let e3 := b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33
  let e4 := b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34
  let e5 := b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35
  let q0 := s6 + s9 - s15
  let q1 := s7 + s10 - s16
  let q2 := s8 + s11 - s17
  let q3 := s9 + s12
  let q4 := s10 + s13
  let q5 := s11 + s14
  let q6 := s12 + s15
  let q7 := s13 + s16
  let q8 := s14 + s17
  let q9 := s15
  let q10 := s16
  let q11 := s17
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
      monomial 11 q11
  let R : Polynomial Int :=
    monomial 0 e0 + monomial 1 e1 + monomial 2 e2 +
      monomial 3 e3 + monomial 4 e4 + monomial 5 e5
  have hresidue : cyclotomic 18 Int ∣
      ∑ i : Fin 36, monomial (i.val % 18) (b i) :=
    cyclotomic_dvd_projection36_residueMask_of_dvd (by norm_num) b hdiv
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
      (∑ i : Fin 36, monomial (i.val % 18) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 18) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  have hidentity :
      (∑ i : Fin 36, monomial (i.val % 18) (b i)) -
          cyclotomic 18 Int * Q = R := by
    rw [cyclotomic_eighteen_eq_int]
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, e0, e1, e2, e3, e4, e5, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, Q, R]
    rw [hsum]
    rw [Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial (n % 18) (bn n)) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    simp only [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    ring
  have hRdiv : cyclotomic 18 Int ∣ R := by
    rw [← hidentity]
    exact dvd_sub hresidue (dvd_mul_right _ _)
  have hRdegree : R.degree < (6 : Nat) := by
    apply (degree_lt_iff_coeff_zero R 6).2
    intro m hm
    have hmNat : 6 ≤ m := by exact_mod_cast hm
    have h0 : (0 : Nat) ≠ m := by omega
    have h1 : (1 : Nat) ≠ m := by omega
    have h2 : (2 : Nat) ≠ m := by omega
    have h3 : (3 : Nat) ≠ m := by omega
    have h4 : (4 : Nat) ≠ m := by omega
    have h5 : (5 : Nat) ≠ m := by omega
    simp only [R, coeff_add, coeff_monomial, if_neg h0, if_neg h1,
      if_neg h2, if_neg h3, if_neg h4, if_neg h5, add_zero]
  have hRzero : R = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hRdiv
    rw [degree_cyclotomic, show Nat.totient 18 = 6 by decide]
    exact hRdegree
  have h0 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hRzero
  have h1 := congrArg (fun P : Polynomial Int ↦ P.coeff 1) hRzero
  have h2 := congrArg (fun P : Polynomial Int ↦ P.coeff 2) hRzero
  have h3 := congrArg (fun P : Polynomial Int ↦ P.coeff 3) hRzero
  have h4 := congrArg (fun P : Polynomial Int ↦ P.coeff 4) hRzero
  have h5 := congrArg (fun P : Polynomial Int ↦ P.coeff 5) hRzero
  simp only [R, coeff_add, coeff_monomial] at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  dsimp only [e0, e1, e2, e3, e4, e5] at h0 h1 h2 h3 h4 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

#print axioms cyclotomic_eighteen_eq_int
#print axioms projection36_phi18_remainders


end Fuglede
