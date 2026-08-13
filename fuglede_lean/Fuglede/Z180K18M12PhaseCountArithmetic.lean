import Fuglede.Z180K18M12PhaseOrientation
import Fuglede.Z180K12Projection36Remainders3_12
import Fuglede.Z180K18M12RootParity
import Mathlib.Tactic

/-!
# `Phi_12` coefficient identities for normalized pair-phase counts

This is the integral algebra in block B.  A degree-eleven phase-count
polynomial whose difference from one is divisible by `Phi_12` satisfies the
four standard remainder equations.  Three of them are packaged directly as
the `Z180K18M12PhaseCounts` record consumed by the table-free parity kernel.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

/-- Mask of the twelve normalized phase multiplicities in one level. -/
noncomputable def z180K18M12NormalizedPhasePolynomial
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) : Polynomial Int :=
  ∑ j : Fin 12,
    monomial j.val (z180K18M12NormalizedPhaseCount p shift c j)

/-- The four independent coefficient equations for a phase polynomial whose
primitive-twelfth value is one. -/
theorem z180_k18_m12_phase_remainders_of_phi12_dvd
    (count : Fin 12 → Int)
    (hdiv : cyclotomic 12 Int ∣
      (∑ j : Fin 12, monomial j.val (count j)) - 1) :
    count 0 - count 4 - count 6 + count 10 = 1 ∧
    count 1 - count 5 - count 7 + count 11 = 0 ∧
    count 2 + count 4 - count 8 - count 10 = 0 ∧
    count 3 + count 5 - count 9 - count 11 = 0 := by
  let c0 := count 0
  let c1 := count 1
  let c2 := count 2
  let c3 := count 3
  let c4 := count 4
  let c5 := count 5
  let c6 := count 6
  let c7 := count 7
  let c8 := count 8
  let c9 := count 9
  let c10 := count 10
  let c11 := count 11
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
  let e0 := c0 - c4 - c6 + c10 - 1
  let e1 := c1 - c5 - c7 + c11
  let e2 := c2 + c4 - c8 - c10
  let e3 := c3 + c5 - c9 - c11
  let R : Polynomial Int :=
    monomial 0 e0 + monomial 1 e1 + monomial 2 e2 + monomial 3 e3
  have hPform :
      (∑ j : Fin 12, monomial j.val (count j)) = P := by
    let cn : Nat → Int := fun n =>
      count ⟨n % 12, Nat.mod_lt n (by norm_num)⟩
    have hcn (j : Fin 12) : cn j.val = count j := by
      apply congrArg count
      apply Fin.ext
      simp [cn, Nat.mod_eq_of_lt j.isLt]
    have hcountsum :
        (∑ j : Fin 12, monomial j.val (count j)) =
          ∑ j : Fin 12, monomial j.val (cn j.val) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcn j]
    rw [hcountsum, Fin.sum_univ_eq_sum_range
      (fun n => monomial n (cn n)) 12]
    dsimp only [P, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]
    norm_num [Finset.sum_range_succ, cn]
    rfl
  have hPdiv : cyclotomic 12 Int ∣ P - 1 := by
    rw [hPform] at hdiv
    exact hdiv
  have hidentity : (P - 1) - cyclotomic 12 Int * Q = R := by
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
  have h0 := congrArg (fun S : Polynomial Int => S.coeff 0) hRzero
  have h1 := congrArg (fun S : Polynomial Int => S.coeff 1) hRzero
  have h2 := congrArg (fun S : Polynomial Int => S.coeff 2) hRzero
  have h3 := congrArg (fun S : Polynomial Int => S.coeff 3) hRzero
  simp only [R, coeff_add, coeff_monomial] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  dsimp only [e0, e1, e2, e3, c0, c1, c2, c3, c4, c5, c6, c7,
    c8, c9, c10, c11] at h0 h1 h2 h3
  exact ⟨by linarith only [h0], h1, h2, h3⟩

/-- Package the three equations needed by `Z180K18M12RootParity`. -/
def z180K18M12PhaseCounts_of_phi12_dvd
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5)
    (hdiv : cyclotomic 12 Int ∣
      z180K18M12NormalizedPhasePolynomial p shift c - 1) :
    Z180K18M12PhaseCounts :=
  let h' :
      cyclotomic 12 Int ∣
        (∑ j : Fin 12,
          monomial j.val (z180K18M12NormalizedPhaseCount p shift c j)) - 1 := by
    simpa only [z180K18M12NormalizedPhasePolynomial] using hdiv
  let h := z180_k18_m12_phase_remainders_of_phi12_dvd
    (z180K18M12NormalizedPhaseCount p shift c) h'
  {
    count := z180K18M12NormalizedPhaseCount p shift c
    h0 := h.1
    h1 := h.2.1
    h3 := h.2.2.2
  }

@[simp]
theorem z180K18M12PhaseCounts_of_phi12_dvd_count
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5)
    (hdiv : cyclotomic 12 Int ∣
      z180K18M12NormalizedPhasePolynomial p shift c - 1) :
    (z180K18M12PhaseCounts_of_phi12_dvd p shift c hdiv).count =
      z180K18M12NormalizedPhaseCount p shift c := by
  rfl

#print axioms z180_k18_m12_phase_remainders_of_phi12_dvd
#print axioms z180K18M12PhaseCounts_of_phi12_dvd

end Fuglede
