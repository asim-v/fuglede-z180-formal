import Fuglede.Z180K30ExceptionalCoeffEvalDefsV71Fix

/-!
# Injectivity of exact evaluation for the K30 coefficient basis

This module proves the polynomial coefficient formula, the degree bound, and
injectivity of evaluation on well-formed coefficient lists.  All list access
arguments recurse directly through `List.getD`; no auxiliary `getD_eq_get*`
API is required.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

open Polynomial
open scoped BigOperators

noncomputable section

theorem coeffPolynomialV71Fix_coeff_lt
    (c : Coeff) (n : Nat) (hn : n < 12) :
    (coeffPolynomialV71Fix c).coeff n = c.getD n 0 := by
  classical
  simp only [coeffPolynomialV71Fix, finsetSum_coeff]
  let target : Fin 12 := ⟨n, hn⟩
  calc
    (∑ i : Fin 12,
        (Polynomial.monomial i.val (c.getD i.val 0)).coeff n) =
        (Polynomial.monomial target.val
          (c.getD target.val 0)).coeff n := by
      apply Finset.sum_eq_single target
      · intro i _hi hine
        simp only [Polynomial.coeff_monomial]
        split_ifs with hval
        · exfalso
          apply hine
          apply Fin.ext
          simpa [target] using hval
        · rfl
      · simp
    _ = c.getD n 0 := by
      simp [target]

theorem coeffPolynomialV71Fix_coeff_ge
    (c : Coeff) (n : Nat) (hn : 12 ≤ n) :
    (coeffPolynomialV71Fix c).coeff n = 0 := by
  classical
  simp only [coeffPolynomialV71Fix, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _hi
  have hi : i.val < 12 := i.isLt
  simp only [Polynomial.coeff_monomial]
  split_ifs with hval
  · omega
  · rfl

theorem coeffPolynomialV71Fix_coeff (c : Coeff) (n : Nat) :
    (coeffPolynomialV71Fix c).coeff n =
      if n < 12 then c.getD n 0 else 0 := by
  by_cases hn : n < 12
  · rw [if_pos hn]
    exact coeffPolynomialV71Fix_coeff_lt c n hn
  · rw [if_neg hn]
    exact coeffPolynomialV71Fix_coeff_ge c n (Nat.le_of_not_gt hn)

theorem coeffPolynomialV71Fix_degree_lt (c : Coeff) :
    (coeffPolynomialV71Fix c).degree < (12 : WithBot Nat) := by
  apply (Polynomial.degree_lt_iff_coeff_zero
    (coeffPolynomialV71Fix c) 12).2
  intro n hn
  exact coeffPolynomialV71Fix_coeff_ge c n hn

private theorem list_eq_of_getD_eq_v71Fix
    {alpha : Type*} (fallback : alpha)
    {left right : List alpha}
    (hlen : left.length = right.length)
    (hgetD : ∀ n, n < left.length →
      left.getD n fallback = right.getD n fallback) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons b right =>
          simp at hlen
  | cons a left ih =>
      cases right with
      | nil =>
          simp at hlen
      | cons b right =>
          have hab : a = b := by
            have hzero := hgetD 0 (by simp)
            simpa [List.getD] using hzero
          have hlenTail : left.length = right.length := by
            simpa using hlen
          have hgetDTail : ∀ n, n < left.length →
              left.getD n fallback = right.getD n fallback := by
            intro n hn
            have hsucc := hgetD (Nat.succ n) (by
              simpa using Nat.succ_lt_succ hn)
            simpa [List.getD] using hsucc
          subst b
          exact congrArg (List.cons a) (ih hlenTail hgetDTail)

private theorem coeffPolynomialV71Fix_zero :
    coeffPolynomialV71Fix coeffZero = 0 := by
  ext n
  by_cases hn : n < 12
  · rw [coeffPolynomialV71Fix_coeff_lt coeffZero n hn]
    interval_cases n <;> simp [coeffZero, List.getD]
  · rw [coeffPolynomialV71Fix_coeff_ge coeffZero n
      (Nat.le_of_not_gt hn)]
    simp

private theorem coeffPolynomialV71Fix_scalar (a : Int) :
    coeffPolynomialV71Fix (scalarCoeff a) = Polynomial.C a := by
  ext n
  by_cases hn : n < 12
  · rw [coeffPolynomialV71Fix_coeff_lt (scalarCoeff a) n hn]
    interval_cases n <;>
      simp [scalarCoeff, List.getD, Polynomial.coeff_C]
  · have hge : 12 ≤ n := Nat.le_of_not_gt hn
    have hn0 : n ≠ 0 := by omega
    rw [coeffPolynomialV71Fix_coeff_ge (scalarCoeff a) n hge]
    simp [Polynomial.coeff_C, hn0]

private theorem coeffAdd_getD_of_lt_length_v71Fix
    (left right : Coeff) (n : Nat)
    (hleft : n < left.length) (hright : n < right.length) :
    (coeffAdd left right).getD n 0 =
      left.getD n 0 + right.getD n 0 := by
  induction n generalizing left right with
  | zero =>
      cases left with
      | nil => simp at hleft
      | cons a left =>
          cases right with
          | nil => simp at hright
          | cons b right => rfl
  | succ n ih =>
      cases left with
      | nil => simp at hleft
      | cons a left =>
          cases right with
          | nil => simp at hright
          | cons b right =>
              have hleftTail : n < left.length := by
                simpa using hleft
              have hrightTail : n < right.length := by
                simpa using hright
              change
                (coeffAdd left right).getD n 0 =
                  left.getD n 0 + right.getD n 0
              exact ih left right hleftTail hrightTail

private theorem coeffAdd_getD_of_lt_v71Fix
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right)
    (n : Nat) (hn : n < 12) :
    (coeffAdd left right).getD n 0 =
      left.getD n 0 + right.getD n 0 := by
  have hleftLen : left.length = 12 := by
    simpa [CoeffWF] using hleft
  have hrightLen : right.length = 12 := by
    simpa [CoeffWF] using hright
  apply coeffAdd_getD_of_lt_length_v71Fix left right n
  · simpa [hleftLen] using hn
  · simpa [hrightLen] using hn

private theorem coeffPolynomialV71Fix_add
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    coeffPolynomialV71Fix (coeffAdd left right) =
      coeffPolynomialV71Fix left + coeffPolynomialV71Fix right := by
  ext n
  by_cases hn : n < 12
  · simp only [Polynomial.coeff_add]
    rw [coeffPolynomialV71Fix_coeff_lt (coeffAdd left right) n hn,
      coeffPolynomialV71Fix_coeff_lt left n hn,
      coeffPolynomialV71Fix_coeff_lt right n hn]
    exact coeffAdd_getD_of_lt_v71Fix hleft hright n hn
  · have hge : 12 ≤ n := Nat.le_of_not_gt hn
    simp only [Polynomial.coeff_add]
    rw [coeffPolynomialV71Fix_coeff_ge (coeffAdd left right) n hge,
      coeffPolynomialV71Fix_coeff_ge left n hge,
      coeffPolynomialV71Fix_coeff_ge right n hge]
    simp

@[simp]
theorem evalCoeffV71Fix_coeffZero :
    evalCoeffV71Fix coeffZero = 0 := by
  unfold evalCoeffV71Fix
  rw [coeffPolynomialV71Fix_zero]
  simp

@[simp]
theorem evalCoeffV71Fix_scalarCoeff (a : Int) :
    evalCoeffV71Fix (scalarCoeff a) = (a : Complex) := by
  unfold evalCoeffV71Fix
  rw [coeffPolynomialV71Fix_scalar]
  simp

theorem evalCoeffV71Fix_coeffAdd
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right) :
    evalCoeffV71Fix (coeffAdd left right) =
      evalCoeffV71Fix left + evalCoeffV71Fix right := by
  unfold evalCoeffV71Fix
  rw [coeffPolynomialV71Fix_add hleft hright]
  simp

theorem evalCoeffV71Fix_injective_of_wf
    {left right : Coeff}
    (hleft : CoeffWF left) (hright : CoeffWF right)
    (heval : evalCoeffV71Fix left = evalCoeffV71Fix right) :
    left = right := by
  let P := coeffPolynomialV71Fix left - coeffPolynomialV71Fix right
  have hroot : Polynomial.aeval zeta36V71Fix P = 0 := by
    dsimp only [P]
    simpa [evalCoeffV71Fix] using sub_eq_zero.mpr heval
  have hdvd : Polynomial.cyclotomic 36 Int ∣ P :=
    (Fuglede.cyclotomic_dvd_iff_aeval_primitive
      (by norm_num) zeta36V71Fix_isPrimitiveRoot P).2 hroot
  have hdegree : P.degree < (12 : WithBot Nat) := by
    dsimp only [P]
    exact (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt
        (coeffPolynomialV71Fix_degree_lt left)
        (coeffPolynomialV71Fix_degree_lt right))
  have htotient : Nat.totient 36 = 12 := by decide
  have hcyclotomicDegree :
      (Polynomial.cyclotomic 36 Int).degree =
        (12 : WithBot Nat) := by
    simpa [htotient] using
      (Polynomial.degree_cyclotomic 36 Int)
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
    rw [hcyclotomicDegree]
    exact hdegree
  have hpolynomial :
      coeffPolynomialV71Fix left = coeffPolynomialV71Fix right := by
    exact sub_eq_zero.mp (by simpa [P] using hPzero)
  have hleftLen : left.length = 12 := by
    simpa [CoeffWF] using hleft
  have hrightLen : right.length = 12 := by
    simpa [CoeffWF] using hright
  apply list_eq_of_getD_eq_v71Fix (0 : Int)
  · exact hleftLen.trans hrightLen.symm
  · intro n hnleft
    have hn : n < 12 := by
      simpa [hleftLen] using hnleft
    have hcoeff := congrArg
      (fun Q : Polynomial Int => Q.coeff n) hpolynomial
    rw [coeffPolynomialV71Fix_coeff_lt left n hn,
      coeffPolynomialV71Fix_coeff_lt right n hn] at hcoeff
    exact hcoeff

#print axioms coeffPolynomialV71Fix_coeff
#print axioms coeffPolynomialV71Fix_degree_lt
#print axioms evalCoeffV71Fix_coeffAdd
#print axioms evalCoeffV71Fix_injective_of_wf

end
end Fuglede.Z180K30ExceptionalRawV2
