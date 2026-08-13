import Fuglede.Z180K6ResiduePattern
import Fuglede.Z180K12Projection36Phi6
import Mathlib.Tactic

/-!
# Compact exclusion of orders two and three at cardinality six

Instead of expanding all thirty-six projected coordinates, this module
groups them into their six residue classes.  The `(4,1,1)` normal form then
contradicts divisibility by either `Phi_2` or `Phi_3` through polynomials of
degree at most five.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The projected indicator after grouping its coefficients by exponents
modulo six. -/
noncomputable def z180K6ResiduePolynomial6
    (b : Fin 36 → Int) : Polynomial Int :=
  monomial 0 (z180K6ResidueSixSum b 0) +
  monomial 1 (z180K6ResidueSixSum b 1) +
  monomial 2 (z180K6ResidueSixSum b 2) +
  monomial 3 (z180K6ResidueSixSum b 3) +
  monomial 4 (z180K6ResidueSixSum b 4) +
  monomial 5 (z180K6ResidueSixSum b 5)

/-- Grouping the already reduced indicator by the six fibres does not
change the polynomial. -/
theorem projection36ResidueMask6_eq_k6ResiduePolynomial6
    (b : Fin 36 → Int) :
    projection36ResidueMask6 b = z180K6ResiduePolynomial6 b := by
  classical
  let g : Fin 36 → Fin 6 := fun i => ⟨i.val % 6, Nat.mod_lt _ (by norm_num)⟩
  let f : Fin 36 → Polynomial Int :=
    fun i => monomial (i.val % 6) (b i)
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Fin 36)) (Finset.univ : Finset (Fin 6)) g f
  have hfilter :
      (Finset.univ : Finset (Fin 36)).filter
          (fun i => g i ∈ (Finset.univ : Finset (Fin 6))) =
        Finset.univ := by
    simp
  rw [hfilter] at hfiber
  have hgroup (r : Fin 6) :
      ∑ i ∈ (Finset.univ : Finset (Fin 36)).filter (fun i => g i = r),
          f i =
        monomial r.val (z180K6ResidueSixSum b (r.val : ZMod 6)) := by
    have hset :
        (Finset.univ : Finset (Fin 36)).filter (fun i => g i = r) =
          z180Projection36ResidueSixIndices (r.val : ZMod 6) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_z180Projection36ResidueSixIndices_iff]
      dsimp only [g]
      constructor
      · intro h
        apply ZMod.val_injective
        simpa [Nat.mod_eq_of_lt r.isLt] using congrArg Fin.val h
      · intro h
        apply Fin.ext
        simpa [Nat.mod_eq_of_lt r.isLt] using congrArg ZMod.val h
    rw [hset]
    calc
      (∑ i ∈ z180Projection36ResidueSixIndices (r.val : ZMod 6), f i) =
          ∑ i ∈ z180Projection36ResidueSixIndices (r.val : ZMod 6),
            monomial r.val (b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [f]
        have hmod : i.val % 6 = r.val := by
          have hz := (mem_z180Projection36ResidueSixIndices_iff
            (r.val : ZMod 6) i).mp hi
          simpa [Nat.mod_eq_of_lt r.isLt] using congrArg ZMod.val hz
        rw [hmod]
      _ = monomial r.val
          (∑ i ∈ z180Projection36ResidueSixIndices (r.val : ZMod 6), b i) := by
        simp_rw [← C_mul_X_pow_eq_monomial]
        rw [← Finset.sum_mul]
        simp
      _ = monomial r.val
          (z180K6ResidueSixSum b (r.val : ZMod 6)) := by
        rw [sum_z180Projection36ResidueSixIndices]
  rw [projection36ResidueMask6]
  change (∑ i : Fin 36, f i) = _
  rw [← hfiber]
  apply Eq.trans (Finset.sum_congr rfl (fun r _ => hgroup r))
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  norm_num [z180K6ResiduePolynomial6, Fin.sum_univ_succ,
    z180K6ResidueSixSum, hv0, hv1, hv2, hv3, hv4, hv5]
  abel

private theorem cyclotomic_dvd_X_pow_sub_mod_six
    (m n : Nat) (hm : m ∣ 6) :
    cyclotomic m Int ∣
      (X : Polynomial Int) ^ n - X ^ (n % 6) := by
  have hperiod : (X ^ m - 1 : Polynomial Int) ∣ X ^ 6 - 1 :=
    dvd_pow_sub_one_of_dvd hm
  have hcyclo : cyclotomic m Int ∣ X ^ 6 - 1 :=
    (cyclotomic.dvd_X_pow_sub_one m Int).trans hperiod
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
  have hsix : (X ^ 6 - 1 : Polynomial Int) ∣
      X ^ n - X ^ (n % 6) := by
    rw [hpow]
    simpa [mul_sub] using hmul
  exact hcyclo.trans hsix

private theorem cyclotomic_dvd_monomial_sub_mod_six
    (m n : Nat) (hm : m ∣ 6) (c : Int) :
    cyclotomic m Int ∣
      monomial n c - monomial (n % 6) c := by
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    ← mul_sub]
  exact dvd_mul_of_dvd_right (cyclotomic_dvd_X_pow_sub_mod_six m n hm) _

/-- Every cyclotomic factor whose index divides six sees the full indicator
and its exponent-six reduction as the same polynomial. -/
theorem cyclotomic_dvd_projection36Indicator_sub_residue6
    (b : Fin 36 → Int) (m : Nat) (hm : m ∣ 6) :
    cyclotomic m Int ∣
      projection36IndicatorMask b - projection36ResidueMask6 b := by
  have hs : cyclotomic m Int ∣
      ∑ i : Fin 36,
        (monomial i.val (b i) - monomial (i.val % 6) (b i)) := by
    apply Finset.dvd_sum
    intro i hi
    exact cyclotomic_dvd_monomial_sub_mod_six m i.val hm (b i)
  simpa [projection36IndicatorMask, projection36ResidueMask6,
    Finset.sum_sub_distrib] using hs

private theorem cyclotomic_dvd_k6ResiduePolynomial6_of_indicator
    (b : Fin 36 → Int) (m : Nat) (hm : m ∣ 6)
    (hdiv : cyclotomic m Int ∣ projection36IndicatorMask b) :
    cyclotomic m Int ∣ z180K6ResiduePolynomial6 b := by
  have hdiff := cyclotomic_dvd_projection36Indicator_sub_residue6 b m hm
  have hresidue : cyclotomic m Int ∣ projection36ResidueMask6 b := by
    have hsub := dvd_sub hdiv hdiff
    simpa using hsub
  rw [projection36ResidueMask6_eq_k6ResiduePolynomial6] at hresidue
  exact hresidue

private theorem phi2_not_dvd_k6ResiduePolynomial6_of_pattern
    (b : Fin 36 → Int) (hpattern : Z180K6ResidueSixPattern b) :
    ¬ cyclotomic 2 Int ∣ z180K6ResiduePolynomial6 b := by
  intro hdiv
  have hroot : eval (-1 : Int) (cyclotomic 2 Int) = 0 := by
    rw [cyclotomic_two]
    norm_num
  have heval := eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hroot
  simp only [z180K6ResiduePolynomial6, eval_add, eval_monomial] at heval
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  norm_num [z180K6ResidueSixSum, hv0, hv1, hv2, hv3, hv4, hv5] at heval
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

private noncomputable def z180K6ResiduePolynomial3
    (b : Fin 36 → Int) : Polynomial Int :=
  monomial 0 (z180K6ResidueSixSum b 0 + z180K6ResidueSixSum b 3) +
  monomial 1 (z180K6ResidueSixSum b 1 + z180K6ResidueSixSum b 4) +
  monomial 2 (z180K6ResidueSixSum b 2 + z180K6ResidueSixSum b 5)

private theorem cyclotomic_three_dvd_residue6_sub_residue3
    (b : Fin 36 → Int) :
    cyclotomic 3 Int ∣
      z180K6ResiduePolynomial6 b - z180K6ResiduePolynomial3 b := by
  let q : Polynomial Int :=
    (X - 1) *
      (monomial 0 (z180K6ResidueSixSum b 3) +
       monomial 1 (z180K6ResidueSixSum b 4) +
       monomial 2 (z180K6ResidueSixSum b 5))
  refine ⟨q, ?_⟩
  dsimp only [q, z180K6ResiduePolynomial6, z180K6ResiduePolynomial3]
  rw [cyclotomic_three]
  simp_rw [← C_mul_X_pow_eq_monomial]
  simp only [map_add]
  ring

private theorem phi3_dvd_quadratic_coefficients_equal
    (c0 c1 c2 : Int)
    (hdiv : cyclotomic 3 Int ∣
      monomial 0 c0 + monomial 1 c1 + monomial 2 c2) :
    c0 - c2 = 0 ∧ c1 - c2 = 0 := by
  let R : Polynomial Int :=
    monomial 0 c0 + monomial 1 c1 + monomial 2 c2
  let D : Polynomial Int := R - monomial 0 c2 * cyclotomic 3 Int
  have hRdiv : cyclotomic 3 Int ∣ R := by simpa only [R] using hdiv
  have hDdiv : cyclotomic 3 Int ∣ D := by
    apply dvd_sub hRdiv
    exact dvd_mul_of_dvd_right (dvd_refl (cyclotomic 3 Int)) _
  have hDform :
      D = monomial 0 (c0 - c2) + monomial 1 (c1 - c2) := by
    dsimp only [D, R]
    rw [cyclotomic_three]
    simp_rw [← C_mul_X_pow_eq_monomial]
    simp only [map_sub]
    ring
  have hDdegree : D.degree < (2 : WithBot Nat) := by
    rw [hDform]
    apply (degree_lt_iff_coeff_zero _ 2).2
    intro n hn
    have hn2 : 2 ≤ n := by exact_mod_cast hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have h1n : 1 ≠ n := Ne.symm hn1
    simp [monomial_zero_left,
      Mathlib.Tactic.ComputeDegree.coeff_intCast_ite,
      coeff_monomial, hn0, h1n]
  have hcycloDegree : (cyclotomic 3 Int).degree = 2 := by
    rw [degree_cyclotomic, show Nat.totient 3 = 2 by decide]
    norm_num
  have hDzero : D = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hDdiv
    rw [hcycloDegree]
    exact hDdegree
  have hc0 := congrArg (fun P : Polynomial Int => P.coeff 0) hDzero
  have hc1 := congrArg (fun P : Polynomial Int => P.coeff 1) hDzero
  rw [hDform] at hc0 hc1
  norm_num [monomial_zero_left,
    Mathlib.Tactic.ComputeDegree.coeff_intCast_ite,
    coeff_monomial] at hc0 hc1
  exact ⟨hc0, hc1⟩

private theorem phi3_not_dvd_k6ResiduePolynomial6_of_pattern
    (b : Fin 36 → Int) (hpattern : Z180K6ResidueSixPattern b) :
    ¬ cyclotomic 3 Int ∣ z180K6ResiduePolynomial6 b := by
  intro hdiv
  have hsmall : cyclotomic 3 Int ∣ z180K6ResiduePolynomial3 b := by
    have hdiff := cyclotomic_three_dvd_residue6_sub_residue3 b
    have hsub := dvd_sub hdiv hdiff
    simpa using hsub
  obtain ⟨h0, h1⟩ := phi3_dvd_quadratic_coefficients_equal
    (z180K6ResidueSixSum b 0 + z180K6ResidueSixSum b 3)
    (z180K6ResidueSixSum b 1 + z180K6ResidueSixSum b 4)
    (z180K6ResidueSixSum b 2 + z180K6ResidueSixSum b 5)
    (by simpa only [z180K6ResiduePolynomial3] using hsmall)
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  norm_num [z180K6ResidueSixSum, hv0, hv1, hv2, hv3, hv4, hv5] at h0 h1
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

/-- The cardinality-six projected normal form rules out `Phi_2`. -/
theorem z180_not_phi2_dvd_of_k6_projection_residue_pattern_compact
    (X : Finset (ZMod 180))
    (hpattern : Z180K6ResidueSixPattern
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int))) :
    ¬ cyclotomic 2 Int ∣ maskPolynomial 180 X := by
  intro hmask
  have hprojected : cyclotomic 2 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 2 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  have hindicator : cyclotomic 2 Int ∣
      projection36IndicatorMask
        (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) := by
    simpa only [projection36IndicatorMask] using hprojected
  exact phi2_not_dvd_k6ResiduePolynomial6_of_pattern _ hpattern
    (cyclotomic_dvd_k6ResiduePolynomial6_of_indicator _ 2 (by norm_num) hindicator)

/-- The cardinality-six projected normal form rules out `Phi_3`. -/
theorem z180_not_phi3_dvd_of_k6_projection_residue_pattern_compact
    (X : Finset (ZMod 180))
    (hpattern : Z180K6ResidueSixPattern
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int))) :
    ¬ cyclotomic 3 Int ∣ maskPolynomial 180 X := by
  intro hmask
  have hprojected : cyclotomic 3 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 3 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  have hindicator : cyclotomic 3 Int ∣
      projection36IndicatorMask
        (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) := by
    simpa only [projection36IndicatorMask] using hprojected
  exact phi3_not_dvd_k6ResiduePolynomial6_of_pattern _ hpattern
    (cyclotomic_dvd_k6ResiduePolynomial6_of_indicator _ 3 (by norm_num) hindicator)

#print axioms projection36ResidueMask6_eq_k6ResiduePolynomial6
#print axioms z180_not_phi2_dvd_of_k6_projection_residue_pattern_compact
#print axioms z180_not_phi3_dvd_of_k6_projection_residue_pattern_compact

end Fuglede
