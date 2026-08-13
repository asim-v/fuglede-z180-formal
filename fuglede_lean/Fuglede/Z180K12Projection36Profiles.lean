import Fuglede.Z180K12Projection36Remainders36
import Mathlib.Tactic

/-!
# Uniform modulo-four profile of the 36-coordinate projection

The forced order-two and order-four cyclotomic zeros, together with
cardinality twelve, make all four residue counts equal to three.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem cyclotomic_four_eq_int :
    cyclotomic 4 Int = X ^ 2 + 1 := by
  rw [show 4 = 2 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ]
  ring

/-- The concrete modulo-four margins forced by `Phi_2`, `Phi_4`, and
total mass twelve. -/
theorem projection36_mod4_profile
    (b : Fin 36 → Int)
    (hsum : (∑ i : Fin 36, b i) = 12)
    (hdiv2 : cyclotomic 2 Int ∣
      ∑ i : Fin 36, monomial i.val (b i))
    (hdiv4 : cyclotomic 4 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
    b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
    b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
    b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3 := by
  let c0 := b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32
  let c1 := b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33
  let c2 := b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34
  let c3 := b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35
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
  have hresidue2 : cyclotomic 2 Int ∣
      ∑ i : Fin 36, monomial (i.val % 2) (b i) :=
    cyclotomic_dvd_projection36_residueMask_of_dvd (by norm_num) b hdiv2
  have hresidue4 : cyclotomic 4 Int ∣
      ∑ i : Fin 36, monomial (i.val % 4) (b i) :=
    cyclotomic_dvd_projection36_residueMask_of_dvd (by norm_num) b hdiv4
  have hsum2 :
      (∑ i : Fin 36, monomial (i.val % 2) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 2) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  have hsum4 :
      (∑ i : Fin 36, monomial (i.val % 4) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 4) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  let e2 := c0 - c1 + c2 - c3
  let R2 : Polynomial Int := monomial 0 e2
  have hidentity2 :
      (∑ i : Fin 36, monomial (i.val % 2) (b i)) -
          cyclotomic 2 Int * monomial 0 (c1 + c3) = R2 := by
    rw [cyclotomic_two]
    dsimp only [c0, c1, c2, c3, e2, R2]
    rw [hsum2]
    rw [Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial (n % 2) (bn n)) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    simp only [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    ring
  have hR2div : cyclotomic 2 Int ∣ R2 := by
    rw [← hidentity2]
    exact dvd_sub hresidue2 (dvd_mul_right _ _)
  have hR2degree : R2.degree < (1 : Nat) := by
    apply (degree_lt_iff_coeff_zero R2 1).2
    intro m hm
    have hmNat : 1 ≤ m := by exact_mod_cast hm
    have h0 : (0 : Nat) ≠ m := by omega
    simp only [R2, coeff_monomial, if_neg h0]
  have hR2zero : R2 = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hR2div
    rw [degree_cyclotomic, show Nat.totient 2 = 1 by decide]
    exact hR2degree
  have he2 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hR2zero
  simp only [R2, coeff_monomial] at he2
  norm_num at he2
  dsimp only [e2] at he2
  let e40 := c0 - c2
  let e41 := c1 - c3
  let R4 : Polynomial Int := monomial 0 e40 + monomial 1 e41
  have hidentity4 :
      (∑ i : Fin 36, monomial (i.val % 4) (b i)) -
          cyclotomic 4 Int *
            (monomial 0 c2 + monomial 1 c3) = R4 := by
    rw [cyclotomic_four_eq_int]
    dsimp only [c0, c1, c2, c3, e40, e41, R4]
    rw [hsum4]
    rw [Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial (n % 4) (bn n)) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    simp only [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    ring
  have hR4div : cyclotomic 4 Int ∣ R4 := by
    rw [← hidentity4]
    exact dvd_sub hresidue4 (dvd_mul_right _ _)
  have hR4degree : R4.degree < (2 : Nat) := by
    apply (degree_lt_iff_coeff_zero R4 2).2
    intro m hm
    have hmNat : 2 ≤ m := by exact_mod_cast hm
    have h0 : (0 : Nat) ≠ m := by omega
    have h1 : (1 : Nat) ≠ m := by omega
    simp only [R4, coeff_add, coeff_monomial, if_neg h0, if_neg h1,
      add_zero]
  have hR4zero : R4 = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hR4div
    rw [degree_cyclotomic, show Nat.totient 4 = 2 by decide]
    exact hR4degree
  have he40 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hR4zero
  have he41 := congrArg (fun P : Polynomial Int ↦ P.coeff 1) hR4zero
  simp only [R4, coeff_add, coeff_monomial] at he40 he41
  norm_num at he40 he41
  dsimp only [e40, e41] at he40 he41
  have hsumScalar :
      (∑ i : Fin 36, b i) = ∑ i : Fin 36, bn i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  have hclasses : c0 + c1 + c2 + c3 = 12 := by
    rw [← hsum]
    rw [hsumScalar]
    rw [Fin.sum_univ_eq_sum_range (fun n ↦ bn n) 36]
    norm_num [Finset.sum_range_succ]
    simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
    dsimp only [c0, c1, c2, c3]
    ring
  dsimp only [c0, c1, c2, c3] at he2 he40 he41 hclasses ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms projection36_mod4_profile

end Fuglede

