import Fuglede.Z180K12Projection36Profiles
import Mathlib.Tactic

/-!
# The two `Phi_6` remainders of the 36-coordinate indicator

This module gives both the integral divisibility criterion and its
characteristic-five consequence used by the `m = 6` defect branch.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def projection36IndicatorMask (b : Fin 36 → Int) : Polynomial Int :=
  ∑ i : Fin 36, monomial i.val (b i)

noncomputable def projection36ResidueMask6 (b : Fin 36 → Int) : Polynomial Int :=
  ∑ i : Fin 36, monomial (i.val % 6) (b i)

def projection36Phi6R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 2 - b 3 + b 5 + b 6 - b 8 - b 9 + b 11 + b 12 - b 14 - b 15 + b 17 + b 18 - b 20 - b 21 + b 23 + b 24 - b 26 - b 27 + b 29 + b 30 - b 32 - b 33 + b 35

def projection36Phi6R1 (b : Fin 36 → Int) : Int :=
  b 1 + b 2 - b 4 - b 5 + b 7 + b 8 - b 10 - b 11 + b 13 + b 14 - b 16 - b 17 + b 19 + b 20 - b 22 - b 23 + b 25 + b 26 - b 28 - b 29 + b 31 + b 32 - b 34 - b 35

private noncomputable def projection36Phi6Quotient
    (b : Fin 36 → Int) : Polynomial Int :=
  let s2 := b 2 + b 8 + b 14 + b 20 + b 26 + b 32
  let s3 := b 3 + b 9 + b 15 + b 21 + b 27 + b 33
  let s4 := b 4 + b 10 + b 16 + b 22 + b 28 + b 34
  let s5 := b 5 + b 11 + b 17 + b 23 + b 29 + b 35
  monomial 0 (s2 + s3 - s5) +
    monomial 1 (s3 + s4) +
    monomial 2 (s4 + s5) +
    monomial 3 s5

noncomputable def projection36Phi6Remainder
    (b : Fin 36 → Int) : Polynomial Int :=
  monomial 0 (projection36Phi6R0 b) +
    monomial 1 (projection36Phi6R1 b)

/-- Exact long-division identity after reducing exponents modulo six. -/
theorem projection36_phi6_residue_identity (b : Fin 36 → Int) :
    projection36ResidueMask6 b -
        cyclotomic 6 Int * projection36Phi6Quotient b =
      projection36Phi6Remainder b := by
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
      projection36ResidueMask6 b =
        ∑ i : Fin 36, monomial (i.val % 6) (bn i.val) := by
    rw [projection36ResidueMask6]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  rw [cyclotomic_six]
  dsimp only [projection36Phi6Quotient]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ monomial (n % 6) (bn n)) 36]
  norm_num [Finset.sum_range_succ]
  simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7, hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15, hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23, hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31, hbn32, hbn33, hbn34, hbn35]
  simp only [projection36Phi6Remainder, projection36Phi6R0,
    projection36Phi6R1, ← C_mul_X_pow_eq_monomial]
  have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
    C_eq_intCast a
  simp_rw [hC]
  push_cast
  ring

private theorem cyclotomic_six_dvd_X_pow_sub_mod (n : Nat) :
    cyclotomic 6 Int ∣
      (X : Polynomial Int) ^ n - X ^ (n % 6) := by
  let k := n / 6
  have hmultiple : 6 ∣ 6 * k := dvd_mul_right 6 k
  have hbase : (X ^ 6 - 1 : Polynomial Int) ∣
      X ^ (6 * k) - 1 := dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ 6 - 1 : Polynomial Int) ∣
      X ^ (n % 6) * (X ^ (6 * k) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : n % 6 + 6 * k = n := by
    simpa [k] using Nat.mod_add_div n 6
  have hpow : (X : Polynomial Int) ^ n =
      X ^ (n % 6) * X ^ (6 * k) := by
    calc
      X ^ n = X ^ (n % 6 + 6 * k) := by rw [hn]
      _ = _ := pow_add _ _ _
  have hperiod : (X ^ 6 - 1 : Polynomial Int) ∣
      X ^ n - X ^ (n % 6) := by
    rw [hpow]
    simpa [mul_sub] using hmul
  exact (cyclotomic.dvd_X_pow_sub_one 6 Int).trans hperiod

private theorem cyclotomic_six_dvd_monomial_sub_mod
    (n : Nat) (c : Int) :
    cyclotomic 6 Int ∣
      monomial n c - monomial (n % 6) c := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    ← mul_sub]
  exact dvd_mul_of_dvd_right (cyclotomic_six_dvd_X_pow_sub_mod n) _

/-- The full indicator and its exponent-six residue are congruent modulo
`Phi_6`. -/
theorem cyclotomic_six_dvd_indicator_sub_residue
    (b : Fin 36 → Int) :
    cyclotomic 6 Int ∣
      projection36IndicatorMask b - projection36ResidueMask6 b := by
  have hs : cyclotomic 6 Int ∣
      ∑ i : Fin 36,
        (monomial i.val (b i) - monomial (i.val % 6) (b i)) := by
    apply Finset.dvd_sum
    intro i hi
    exact cyclotomic_six_dvd_monomial_sub_mod i.val (b i)
  simpa [projection36IndicatorMask, projection36ResidueMask6,
    Finset.sum_sub_distrib] using hs

private theorem degree_projection36Phi6Remainder_lt
    (b : Fin 36 → Int) :
    (projection36Phi6Remainder b).degree < (2 : Nat) := by
  apply (degree_lt_iff_coeff_zero (projection36Phi6Remainder b) 2).2
  intro m hm
  have hmNat : 2 ≤ m := by exact_mod_cast hm
  have h0 : (0 : Nat) ≠ m := by omega
  have h1 : (1 : Nat) ≠ m := by omega
  simp only [projection36Phi6Remainder, coeff_add, coeff_monomial,
    if_neg h0, if_neg h1, add_zero]

/-- Integral `Phi_6` divisibility is equivalent to vanishing of the two
explicit remainders. -/
theorem projection36_phi6_dvd_iff_remainders_zero (b : Fin 36 → Int) :
    cyclotomic 6 Int ∣ projection36IndicatorMask b ↔
      projection36Phi6R0 b = 0 ∧ projection36Phi6R1 b = 0 := by
  constructor
  · intro hdiv
    have hresidue : cyclotomic 6 Int ∣ projection36ResidueMask6 b := by
      have hdiff := cyclotomic_six_dvd_indicator_sub_residue b
      have hsub := dvd_sub hdiv hdiff
      simpa using hsub
    have hRdiv : cyclotomic 6 Int ∣ projection36Phi6Remainder b := by
      rw [← projection36_phi6_residue_identity]
      exact dvd_sub hresidue (dvd_mul_right _ _)
    have hRzero : projection36Phi6Remainder b = 0 := by
      apply eq_zero_of_dvd_of_degree_lt hRdiv
      rw [degree_cyclotomic, show Nat.totient 6 = 2 by decide]
      exact degree_projection36Phi6Remainder_lt b
    have h0 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hRzero
    have h1 := congrArg (fun P : Polynomial Int ↦ P.coeff 1) hRzero
    simp only [projection36Phi6Remainder, coeff_add, coeff_monomial] at h0 h1
    norm_num at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    have hRzero : projection36Phi6Remainder b = 0 := by
      simp [projection36Phi6Remainder, h0, h1]
    have hid := projection36_phi6_residue_identity b
    rw [hRzero] at hid
    have hresidue : cyclotomic 6 Int ∣ projection36ResidueMask6 b := by
      refine ⟨projection36Phi6Quotient b, ?_⟩
      exact sub_eq_zero.mp hid
    have hdiff := cyclotomic_six_dvd_indicator_sub_residue b
    have hadd := dvd_add hdiff hresidue
    simpa using hadd

/-- Characteristic-five `Phi_6` divisibility annihilates both integral
remainders modulo five. -/
theorem projection36_phi6_mod_five_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 6 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    (projection36Phi6R0 b : ZMod 5) = 0 ∧
      (projection36Phi6R1 b : ZMod 5) = 0 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdiffInt := cyclotomic_six_dvd_indicator_sub_residue b
  have hdiffMapped := Polynomial.map_dvd
    (Int.castRingHom (ZMod 5)) hdiffInt
  rw [map_cyclotomic] at hdiffMapped
  have hdiff :
      cyclotomic 6 (ZMod 5) ∣
        (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5)) -
          (projection36ResidueMask6 b).map
            (Int.castRingHom (ZMod 5)) := by
    simpa using hdiffMapped
  have hresidue :
      cyclotomic 6 (ZMod 5) ∣
        (projection36ResidueMask6 b).map
          (Int.castRingHom (ZMod 5)) := by
    have hsub := dvd_sub hdiv hdiff
    simpa using hsub
  have hidMapped := congrArg
    (Polynomial.map (Int.castRingHom (ZMod 5)))
    (projection36_phi6_residue_identity b)
  have hidMapped' :
      (projection36ResidueMask6 b).map
          (Int.castRingHom (ZMod 5)) -
        cyclotomic 6 (ZMod 5) *
          (projection36Phi6Quotient b).map
            (Int.castRingHom (ZMod 5)) =
        (projection36Phi6Remainder b).map
          (Int.castRingHom (ZMod 5)) := by
    simpa only [Polynomial.map_sub, Polynomial.map_mul,
      map_cyclotomic] using hidMapped
  have hRdiv :
      cyclotomic 6 (ZMod 5) ∣
        (projection36Phi6Remainder b).map
          (Int.castRingHom (ZMod 5)) := by
    rw [← hidMapped']
    exact dvd_sub hresidue (dvd_mul_right _ _)
  have hRdegree :
      ((projection36Phi6Remainder b).map
        (Int.castRingHom (ZMod 5))).degree < (2 : Nat) :=
    lt_of_le_of_lt degree_map_le (degree_projection36Phi6Remainder_lt b)
  have hRzero :
      (projection36Phi6Remainder b).map
        (Int.castRingHom (ZMod 5)) = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hRdiv
    rw [degree_cyclotomic, show Nat.totient 6 = 2 by decide]
    exact hRdegree
  have h0 := congrArg
    (fun P : Polynomial (ZMod 5) ↦ P.coeff 0) hRzero
  have h1 := congrArg
    (fun P : Polynomial (ZMod 5) ↦ P.coeff 1) hRzero
  simp only [projection36Phi6Remainder, coeff_map, coeff_add,
    coeff_monomial] at h0 h1
  norm_num at h0 h1
  exact ⟨h0, h1⟩

/-- Integer witnesses for the two multiples of five consumed by the compact
Presburger kernels. -/
theorem projection36_phi6_five_multipliers
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 6 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 : Int,
      projection36Phi6R0 b = 5 * k0 ∧
      projection36Phi6R1 b = 5 * k1 := by
  obtain ⟨h0, h1⟩ := projection36_phi6_mod_five_remainders b hdiv
  have hd0 : (5 : Int) ∣ projection36Phi6R0 b :=
    (CharP.intCast_eq_zero_iff (ZMod 5) 5 _).mp h0
  have hd1 : (5 : Int) ∣ projection36Phi6R1 b :=
    (CharP.intCast_eq_zero_iff (ZMod 5) 5 _).mp h1
  obtain ⟨k0, hk0⟩ := hd0
  obtain ⟨k1, hk1⟩ := hd1
  exact ⟨k0, k1, hk0, hk1⟩

theorem projection36_phi6_remainders_ne_of_not_dvd
    (b : Fin 36 → Int)
    (hnot : ¬ cyclotomic 6 Int ∣ projection36IndicatorMask b) :
    projection36Phi6R0 b ≠ 0 ∨ projection36Phi6R1 b ≠ 0 := by
  by_contra h
  push Not at h
  exact hnot ((projection36_phi6_dvd_iff_remainders_zero b).2 h)

#print axioms projection36_phi6_dvd_iff_remainders_zero
#print axioms projection36_phi6_mod_five_remainders
#print axioms projection36_phi6_five_multipliers
#print axioms projection36_phi6_remainders_ne_of_not_dvd

end Fuglede
