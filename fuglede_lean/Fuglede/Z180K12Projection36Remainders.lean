import Fuglede.Z180K12Projection36Mask
import Mathlib.Tactic

/-!
# Concrete cyclotomic remainders for the 36-coordinate projection

The finite Presburger kernels use explicit integral remainder equations.  This
module derives those equations from genuine polynomial divisibility, without
trusting a precomputed coefficient table.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000
private theorem cyclotomic_dvd_X_pow_sub_mod
    {q n : Nat} (_hq : q ≠ 0) :
    cyclotomic q Int ∣
      (X : Polynomial Int) ^ n - X ^ (n % q) := by
  let k := n / q
  have hmultiple : q ∣ q * k := dvd_mul_right q k
  have hbase : (X ^ q - 1 : Polynomial Int) ∣
      X ^ (q * k) - 1 := dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ q - 1 : Polynomial Int) ∣
      X ^ (n % q) * (X ^ (q * k) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : n % q + q * k = n := by
    simpa [k] using Nat.mod_add_div n q
  have hpow : (X : Polynomial Int) ^ n =
      X ^ (n % q) * X ^ (q * k) := by
    calc
      X ^ n = X ^ (n % q + q * k) := by rw [hn]
      _ = _ := pow_add _ _ _
  have hperiod : (X ^ q - 1 : Polynomial Int) ∣
      X ^ n - X ^ (n % q) := by
    rw [hpow]
    simpa [mul_sub] using hmul
  exact (cyclotomic.dvd_X_pow_sub_one q Int).trans hperiod

private theorem cyclotomic_dvd_monomial_sub_mod
    {q n : Nat} (hq : q ≠ 0) (c : Int) :
    cyclotomic q Int ∣
      monomial n c - monomial (n % q) c := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    ← mul_sub]
  exact dvd_mul_of_dvd_right (cyclotomic_dvd_X_pow_sub_mod hq) _

/-- Reducing all 36 exponents modulo `q` preserves `Phi_q` divisibility. -/
theorem cyclotomic_dvd_projection36_residueMask_of_dvd
    {q : Nat} (hq : q ≠ 0) (b : Fin 36 → Int)
    (hdiv : cyclotomic q Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    cyclotomic q Int ∣
      ∑ i : Fin 36, monomial (i.val % q) (b i) := by
  have hdiff : cyclotomic q Int ∣
      (∑ i : Fin 36, monomial i.val (b i)) -
        ∑ i : Fin 36, monomial (i.val % q) (b i) := by
    have hs : cyclotomic q Int ∣
        ∑ i : Fin 36,
          (monomial i.val (b i) - monomial (i.val % q) (b i)) := by
      apply Finset.dvd_sum
      intro i hi
      exact cyclotomic_dvd_monomial_sub_mod hq (b i)
    simpa [Finset.sum_sub_distrib] using hs
  have hsub := dvd_sub hdiv hdiff
  simpa using hsub

private theorem cyclotomic_nine_eq :
    cyclotomic 9 Int = X ^ 6 + X ^ 3 + 1 := by
  rw [show 9 = 3 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum (by norm_num : Nat.Prime 3)]
  norm_num [Finset.sum_range_succ]
  ring

private theorem X_pow_mul_intCast_eq_monomial (n : Nat) (a : Int) :
    (X : Polynomial Int) ^ n * (a : Polynomial Int) = monomial n a := by
  rw [mul_comm]
  have hC : (a : Polynomial Int) = C a := by
    exact (C_eq_intCast a).symm
  rw [hC, C_mul_X_pow_eq_monomial]

/-- All six integral remainder coefficients modulo `Phi_9`. -/
theorem projection36_phi9_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 9 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33 = 0 ∧
    b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34 = 0 ∧
    b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35 = 0 ∧
    b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33 = 0 ∧
    b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34 = 0 ∧
    b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35 = 0 := by
  let e0 := b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33
  let e1 := b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34
  let e2 := b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35
  let e3 := b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33
  let e4 := b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34
  let e5 := b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35
  let c6 := b 6 + b 15 + b 24 + b 33
  let c7 := b 7 + b 16 + b 25 + b 34
  let c8 := b 8 + b 17 + b 26 + b 35
  let R : Polynomial Int :=
    monomial 0 e0 + monomial 1 e1 + monomial 2 e2 +
      monomial 3 e3 + monomial 4 e4 + monomial 5 e5
  have hresidue : cyclotomic 9 Int ∣
      ∑ i : Fin 36, monomial (i.val % 9) (b i) :=
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
      (∑ i : Fin 36, monomial (i.val % 9) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 9) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  have hidentity :
      (∑ i : Fin 36, monomial (i.val % 9) (b i)) -
          cyclotomic 9 Int *
            (monomial 0 c6 + monomial 1 c7 + monomial 2 c8) = R := by
    rw [cyclotomic_nine_eq]
    dsimp only [R, e0, e1, e2, e3, e4, e5, c6, c7, c8]
    rw [hsum]
    rw [Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial (n % 9) (bn n)) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    simp only [add_mul, mul_add, one_mul, X_pow_mul_monomial]
    norm_num
    simp_rw [X_pow_mul_intCast_eq_monomial]
    abel
  have hRdiv : cyclotomic 9 Int ∣ R := by
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
    rw [degree_cyclotomic, show Nat.totient 9 = 6 by decide]
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

theorem projection36_phi9_remainder_coeff_zero
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 9 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33 = 0 :=
  (projection36_phi9_remainders b hdiv).1

#print axioms projection36_phi9_remainder_coeff_zero
#print axioms projection36_phi9_remainders

end Fuglede
