import Fuglede.Z180K12Projection36Remainders
import Mathlib.Tactic

/-!
# Count remainders for orders three and twelve

The order-three and order-twelve Presburger kernels use the twelve sums of
the 36 projected coordinates over equal residues modulo twelve.  This module
derives their explicit equations from genuine cyclotomic divisibility.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Sum of the three projected coordinates in one class modulo twelve. -/
def projection36Count12 (b : Fin 36 → Int) (r : Fin 12) : Int :=
  b ⟨r.val, by omega⟩ + b ⟨r.val + 12, by omega⟩ +
    b ⟨r.val + 24, by omega⟩

noncomputable def projection36Count12Polynomial
    (b : Fin 36 → Int) : Polynomial Int :=
  ∑ r : Fin 12, monomial r.val (projection36Count12 b r)

theorem projection36_residue12_eq_countPolynomial
    (b : Fin 36 → Int) :
    (∑ i : Fin 36, monomial (i.val % 12) (b i)) =
      projection36Count12Polynomial b := by
  let bn : Nat → Int := fun n ↦
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [bn, Nat.mod_eq_of_lt i.isLt]
  have hsum :
      (∑ i : Fin 36, monomial (i.val % 12) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 12) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  let cn : Nat → Int := fun n ↦
    projection36Count12 b ⟨n % 12, Nat.mod_lt n (by norm_num)⟩
  have hcn (i : Fin 12) : cn i.val = projection36Count12 b i := by
    apply congrArg (projection36Count12 b)
    apply Fin.ext
    simp [cn, Nat.mod_eq_of_lt i.isLt]
  have hcountsum :
      (∑ i : Fin 12, monomial i.val (projection36Count12 b i)) =
        ∑ i : Fin 12, monomial i.val (cn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcn i]
  rw [projection36Count12Polynomial, hsum, hcountsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ monomial (n % 12) (bn n)) 36]
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ monomial n (cn n)) 12]
  norm_num [Finset.sum_range_succ, bn, cn, projection36Count12]
  abel

private theorem projection36_residue3_eq_countPolynomial
    (b : Fin 36 → Int) :
    (∑ i : Fin 36, monomial (i.val % 3) (b i)) =
      monomial 0
        (projection36Count12 b 0 + projection36Count12 b 3 +
          projection36Count12 b 6 + projection36Count12 b 9) +
      monomial 1
        (projection36Count12 b 1 + projection36Count12 b 4 +
          projection36Count12 b 7 + projection36Count12 b 10) +
      monomial 2
        (projection36Count12 b 2 + projection36Count12 b 5 +
          projection36Count12 b 8 + projection36Count12 b 11) := by
  let bn : Nat → Int := fun n ↦
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [bn, Nat.mod_eq_of_lt i.isLt]
  have hsum :
      (∑ i : Fin 36, monomial (i.val % 3) (b i)) =
        ∑ i : Fin 36, monomial (i.val % 3) (bn i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbn i]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun n ↦ monomial (n % 3) (bn n)) 36]
  norm_num [Finset.sum_range_succ, bn, projection36Count12]
  abel

/-- The two independent `Phi_3` equations on the twelve residue counts. -/
theorem projection36_phi3_count12_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 3 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    projection36Count12 b 0 - projection36Count12 b 2 +
        projection36Count12 b 3 - projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 +
        projection36Count12 b 9 - projection36Count12 b 11 = 0 ∧
    projection36Count12 b 1 - projection36Count12 b 2 +
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 - projection36Count12 b 8 +
        projection36Count12 b 10 - projection36Count12 b 11 = 0 := by
  let c0 := projection36Count12 b 0 + projection36Count12 b 3 +
    projection36Count12 b 6 + projection36Count12 b 9
  let c1 := projection36Count12 b 1 + projection36Count12 b 4 +
    projection36Count12 b 7 + projection36Count12 b 10
  let c2 := projection36Count12 b 2 + projection36Count12 b 5 +
    projection36Count12 b 8 + projection36Count12 b 11
  let R : Polynomial Int :=
    monomial 0 c0 + monomial 1 c1 + monomial 2 c2
  let D : Polynomial Int := R - monomial 0 c2 * cyclotomic 3 Int
  have hresidue : cyclotomic 3 Int ∣
      ∑ i : Fin 36, monomial (i.val % 3) (b i) :=
    cyclotomic_dvd_projection36_residueMask_of_dvd (by norm_num) b hdiv
  have hRdiv : cyclotomic 3 Int ∣ R := by
    rw [projection36_residue3_eq_countPolynomial] at hresidue
    simpa only [R, c0, c1, c2] using hresidue
  have hDdiv : cyclotomic 3 Int ∣ D := by
    apply dvd_sub hRdiv
    exact dvd_mul_of_dvd_right (dvd_refl (cyclotomic 3 Int)) _
  have hDform :
      D = monomial 0 (c0 - c2) + monomial 1 (c1 - c2) := by
    dsimp only [D, R]
    rw [cyclotomic_three]
    simp_rw [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    push_cast
    ring
  have hDdegree : D.degree < (2 : WithBot Nat) := by
    rw [hDform]
    apply (degree_lt_iff_coeff_zero _ 2).2
    intro n hn
    have hn2 : 2 ≤ n := by exact_mod_cast hn
    have h0 : (0 : Nat) ≠ n := by omega
    have h1 : (1 : Nat) ≠ n := by omega
    simp only [coeff_add, coeff_monomial, if_neg h0, if_neg h1,
      add_zero]
  have hDzero : D = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hDdiv
    rw [degree_cyclotomic, show Nat.totient 3 = 2 by decide]
    exact hDdegree
  have h0 := congrArg (fun P : Polynomial Int ↦ P.coeff 0) hDzero
  have h1 := congrArg (fun P : Polynomial Int ↦ P.coeff 1) hDzero
  rw [hDform] at h0 h1
  simp only [coeff_add, coeff_monomial] at h0 h1
  norm_num at h0 h1
  dsimp only [c0, c1, c2] at h0 h1
  exact ⟨by linarith only [h0], by linarith only [h1]⟩

theorem cyclotomic_twelve_eq_int :
    cyclotomic 12 Int = X ^ 4 - X ^ 2 + 1 := by
  rw [show 12 = 6 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num)]
  rw [cyclotomic_six]
  simp
  ring

/-- The four independent `Phi_12` equations on the twelve residue counts. -/
theorem projection36_phi12_count12_remainders
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 12 Int ∣
      ∑ i : Fin 36, monomial i.val (b i)) :
    projection36Count12 b 0 - projection36Count12 b 4 -
        projection36Count12 b 6 + projection36Count12 b 10 = 0 ∧
    projection36Count12 b 1 - projection36Count12 b 5 -
        projection36Count12 b 7 + projection36Count12 b 11 = 0 ∧
    projection36Count12 b 2 + projection36Count12 b 4 -
        projection36Count12 b 8 - projection36Count12 b 10 = 0 ∧
    projection36Count12 b 3 + projection36Count12 b 5 -
        projection36Count12 b 9 - projection36Count12 b 11 = 0 := by
  let c0 := projection36Count12 b 0
  let c1 := projection36Count12 b 1
  let c2 := projection36Count12 b 2
  let c3 := projection36Count12 b 3
  let c4 := projection36Count12 b 4
  let c5 := projection36Count12 b 5
  let c6 := projection36Count12 b 6
  let c7 := projection36Count12 b 7
  let c8 := projection36Count12 b 8
  let c9 := projection36Count12 b 9
  let c10 := projection36Count12 b 10
  let c11 := projection36Count12 b 11
  let P : Polynomial Int :=
    monomial 0 c0 + monomial 1 c1 + monomial 2 c2 + monomial 3 c3 +
    monomial 4 c4 + monomial 5 c5 + monomial 6 c6 + monomial 7 c7 +
    monomial 8 c8 + monomial 9 c9 + monomial 10 c10 + monomial 11 c11
  let q0 := c4 + c6 - c10
  let q1 := c5 + c7 - c11
  let q2 := c6 + c8
  let q3 := c7 + c9
  let q4 := c8 + c10
  let q5 := c9 + c11
  let q6 := c10
  let q7 := c11
  let Q : Polynomial Int :=
    monomial 0 q0 + monomial 1 q1 + monomial 2 q2 + monomial 3 q3 +
    monomial 4 q4 + monomial 5 q5 + monomial 6 q6 + monomial 7 q7
  let e0 := c0 - c4 - c6 + c10
  let e1 := c1 - c5 - c7 + c11
  let e2 := c2 + c4 - c8 - c10
  let e3 := c3 + c5 - c9 - c11
  let R : Polynomial Int :=
    monomial 0 e0 + monomial 1 e1 + monomial 2 e2 + monomial 3 e3
  have hresidue : cyclotomic 12 Int ∣
      ∑ i : Fin 36, monomial (i.val % 12) (b i) :=
    cyclotomic_dvd_projection36_residueMask_of_dvd (by norm_num) b hdiv
  have hPform : projection36Count12Polynomial b = P := by
    let cn : Nat → Int := fun n ↦
      projection36Count12 b ⟨n % 12, Nat.mod_lt n (by norm_num)⟩
    have hcn (i : Fin 12) : cn i.val = projection36Count12 b i := by
      apply congrArg (projection36Count12 b)
      apply Fin.ext
      simp [cn, Nat.mod_eq_of_lt i.isLt]
    have hcountsum :
        (∑ i : Fin 12, monomial i.val (projection36Count12 b i)) =
          ∑ i : Fin 12, monomial i.val (cn i.val) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcn i]
    dsimp only [projection36Count12Polynomial]
    rw [hcountsum, Fin.sum_univ_eq_sum_range
      (fun n ↦ monomial n (cn n)) 12]
    dsimp only [P, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
    norm_num [Finset.sum_range_succ, cn]
    rfl
  have hPdiv : cyclotomic 12 Int ∣ P := by
    rw [projection36_residue12_eq_countPolynomial, hPform] at hresidue
    exact hresidue
  have hidentity : P - cyclotomic 12 Int * Q = R := by
    rw [cyclotomic_twelve_eq_int]
    dsimp only [P, Q, R, q0, q1, q2, q3, q4, q5, q6, q7,
      e0, e1, e2, e3]
    simp_rw [← C_mul_X_pow_eq_monomial]
    have hC (a : Int) : (C a : Polynomial Int) = (a : Polynomial Int) :=
      C_eq_intCast a
    simp_rw [hC]
    push_cast
    ring
  have hRdiv : cyclotomic 12 Int ∣ R := by
    rw [← hidentity]
    exact dvd_sub hPdiv (dvd_mul_right _ _)
  have hRdegree : R.degree < (4 : Nat) := by
    apply (degree_lt_iff_coeff_zero R 4).2
    intro n hn
    have hn4 : 4 ≤ n := by exact_mod_cast hn
    have h0 : (0 : Nat) ≠ n := by omega
    have h1 : (1 : Nat) ≠ n := by omega
    have h2 : (2 : Nat) ≠ n := by omega
    have h3 : (3 : Nat) ≠ n := by omega
    simp only [R, coeff_add, coeff_monomial, if_neg h0, if_neg h1,
      if_neg h2, if_neg h3, add_zero]
  have hRzero : R = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hRdiv
    rw [degree_cyclotomic, show Nat.totient 12 = 4 by decide]
    exact hRdegree
  have h0 := congrArg (fun S : Polynomial Int ↦ S.coeff 0) hRzero
  have h1 := congrArg (fun S : Polynomial Int ↦ S.coeff 1) hRzero
  have h2 := congrArg (fun S : Polynomial Int ↦ S.coeff 2) hRzero
  have h3 := congrArg (fun S : Polynomial Int ↦ S.coeff 3) hRzero
  simp only [R, coeff_add, coeff_monomial] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  dsimp only [e0, e1, e2, e3, c0, c1, c2, c3, c4, c5, c6, c7,
    c8, c9, c10, c11] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

#print axioms projection36_phi3_count12_remainders
#print axioms cyclotomic_twelve_eq_int
#print axioms projection36_phi12_count12_remainders

end Fuglede
