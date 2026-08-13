import Fuglede.Z180K18M12PairFibres
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Low-order modulo-nine fibres in the cardinality-eighteen `m = 12` branch

This module proves the first field of
`Z180K18M12PairFibresExtractionInterface`.  The mask is reduced modulo
`X^9 - 1`.  Its `Phi_3` and `Phi_9` factors combine to the geometric sum
`1 + X + ... + X^8`; degree below nine and value eighteen at one then force
every coefficient, hence every residue fibre modulo nine, to equal two.

No high-order or fifth-level geometry is used here.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Integral mask obtained by reducing every exponent modulo nine. -/
noncomputable def z180K18M12NineMask
    (A : Finset (ZMod 180)) : Polynomial Int :=
  A.sum fun x => monomial (ZMod.cast x : ZMod 9).val 1

/-- Coefficients of the projected mask are the modulo-nine fibre sizes. -/
theorem coeff_z180K18M12NineMask
    (A : Finset (ZMod 180)) (r : ZMod 9) :
    (z180K18M12NineMask A).coeff r.val =
      ((z180K18M12NineFiber A r).card : Int) := by
  classical
  simp only [z180K18M12NineMask, finsetSum_coeff, coeff_monomial]
  rw [z180K18M12NineFiber, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxr : (ZMod.cast x : ZMod 9) = r
  · have hval : (ZMod.cast x : ZMod 9).val = r.val := congrArg ZMod.val hxr
    simp [hxr, hval]
  · have hval : (ZMod.cast x : ZMod 9).val ≠ r.val :=
      fun h => hxr (ZMod.val_injective 9 h)
    simp [hxr, hval]

/-- The projected mask has degree strictly below nine. -/
theorem degree_z180K18M12NineMask_lt (A : Finset (ZMod 180)) :
    (z180K18M12NineMask A).degree < (9 : Nat) := by
  apply (degree_lt_iff_coeff_zero (z180K18M12NineMask A) 9).2
  intro m hm
  have hmNat : 9 ≤ m := by exact_mod_cast hm
  simp only [z180K18M12NineMask, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : (ZMod.cast x : ZMod 9).val ≠ m := by
    have hlt : (ZMod.cast x : ZMod 9).val < 9 := (ZMod.cast x : ZMod 9).val_lt
    omega
  rw [coeff_monomial, if_neg hne]

/-- Evaluation at one remembers the original cardinality. -/
theorem eval_one_z180K18M12NineMask (A : Finset (ZMod 180)) :
    (z180K18M12NineMask A).eval 1 = (A.card : Int) := by
  classical
  simp [z180K18M12NineMask, Polynomial.eval_finsetSum]

private theorem z180K18M12_cast9_val (x : ZMod 180) :
    (ZMod.cast x : ZMod 9).val = x.val % 9 := by
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

private theorem z180K18M12_maskPolynomial_eq_sum_monomial
    (A : Finset (ZMod 180)) :
    maskPolynomial 180 A = A.sum (fun x => monomial x.val 1) := by
  classical
  rw [maskPolynomial]
  apply Finset.sum_congr rfl
  intro x hx
  simp [monomial_one_right_eq_X_pow]

/-- One exponent and its residue modulo nine differ by a multiple of
`X^9 - 1`. -/
private theorem z180K18M12_X_pow_sub_projection9_dvd (x : ZMod 180) :
    (X ^ 9 - 1 : Polynomial Int) ∣
      monomial x.val 1 - monomial (ZMod.cast x : ZMod 9).val 1 := by
  rw [monomial_one_right_eq_X_pow, monomial_one_right_eq_X_pow]
  rw [z180K18M12_cast9_val]
  let q := x.val / 9
  have hmultiple : 9 ∣ 9 * q := dvd_mul_right 9 q
  have hbase : (X ^ 9 - 1 : Polynomial Int) ∣ X ^ (9 * q) - 1 :=
    dvd_pow_sub_one_of_dvd hmultiple
  have hmul : (X ^ 9 - 1 : Polynomial Int) ∣
      X ^ (x.val % 9) * (X ^ (9 * q) - 1) :=
    dvd_mul_of_dvd_right hbase _
  have hn : x.val % 9 + 9 * q = x.val := by
    simpa [q] using Nat.mod_add_div x.val 9
  have hpow : X ^ x.val =
      (X : Polynomial Int) ^ (x.val % 9) * X ^ (9 * q) := by
    calc
      X ^ x.val = X ^ (x.val % 9 + 9 * q) := by rw [hn]
      _ = _ := pow_add _ _ _
  rw [hpow]
  simpa [mul_sub] using hmul

/-- The original mask and its exponent projection are congruent modulo
`X^9 - 1`. -/
theorem X_pow_9_sub_one_dvd_mask_sub_z180K18M12NineMask
    (A : Finset (ZMod 180)) :
    (X ^ 9 - 1 : Polynomial Int) ∣
      maskPolynomial 180 A - z180K18M12NineMask A := by
  classical
  rw [z180K18M12_maskPolynomial_eq_sum_monomial, z180K18M12NineMask]
  have hs : (X ^ 9 - 1 : Polynomial Int) ∣
      A.sum (fun x => monomial x.val 1 -
        monomial (ZMod.cast x : ZMod 9).val 1) := by
    apply Finset.dvd_sum
    intro x hx
    exact z180K18M12_X_pow_sub_projection9_dvd x
  simpa [Finset.sum_sub_distrib] using hs

/-- Every cyclotomic factor indexed by a divisor of nine survives exponent
projection modulo nine. -/
theorem cyclotomic_dvd_z180K18M12NineMask_of_dvd_mask
    {m : Nat} (hm9 : m ∣ 9) {A : Finset (ZMod 180)}
    (hdiv : cyclotomic m Int ∣ maskPolynomial 180 A) :
    cyclotomic m Int ∣ z180K18M12NineMask A := by
  have hcycloMod : cyclotomic m Int ∣ (X ^ 9 - 1 : Polynomial Int) :=
    (cyclotomic.dvd_X_pow_sub_one m Int).trans
      (dvd_pow_sub_one_of_dvd hm9)
  have hdiff : cyclotomic m Int ∣
      maskPolynomial 180 A - z180K18M12NineMask A :=
    hcycloMod.trans (X_pow_9_sub_one_dvd_mask_sub_z180K18M12NineMask A)
  have hsub := dvd_sub hdiv hdiff
  simpa using hsub

/-- Product of the two nontrivial cyclotomic factors of `X^9 - 1`. -/
noncomputable def z180K18M12NineCyclotomicProduct : Polynomial Int :=
  cyclotomic 3 Int * cyclotomic 9 Int

theorem z180K18M12NineCyclotomicProduct_mul_X_sub_one :
    z180K18M12NineCyclotomicProduct * (X - 1) = X ^ 9 - 1 := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (by norm_num : 0 < 9) Int
  have hd : (9 : Nat).divisors = {1, 3, 9} := by decide
  rw [hd] at h
  simpa [z180K18M12NineCyclotomicProduct, cyclotomic_one,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit geometric-sum form of the product. -/
theorem z180K18M12NineCyclotomicProduct_eq_geomSum :
    z180K18M12NineCyclotomicProduct =
      Finset.sum (Finset.range 9) (fun i => X ^ i) := by
  let G : Polynomial Int := Finset.sum (Finset.range 9) (fun i => X ^ i)
  have hG : G * (X - 1) = X ^ 9 - 1 := by
    simpa [G] using (geom_sum_mul X 9)
  have hmul : (z180K18M12NineCyclotomicProduct - G) * (X - 1) = 0 := by
    rw [sub_mul, z180K18M12NineCyclotomicProduct_mul_X_sub_one,
      hG, sub_self]
  rcases mul_eq_zero.mp hmul with hzero | hbad
  · exact sub_eq_zero.mp hzero
  · exact False.elim ((X_sub_C_ne_zero (1 : Int)) (by simpa using hbad))

theorem natDegree_z180K18M12NineCyclotomicProduct :
    z180K18M12NineCyclotomicProduct.natDegree = 8 := by
  have h3 : cyclotomic 3 Int ≠ 0 := cyclotomic_ne_zero _ _
  have h9 : cyclotomic 9 Int ≠ 0 := cyclotomic_ne_zero _ _
  simp only [z180K18M12NineCyclotomicProduct]
  rw [natDegree_mul h3 h9]
  simp only [natDegree_cyclotomic]
  decide

theorem z180K18M12NineCyclotomicProduct_ne_zero :
    z180K18M12NineCyclotomicProduct ≠ 0 := by
  simp only [z180K18M12NineCyclotomicProduct]
  exact mul_ne_zero (cyclotomic_ne_zero _ _) (cyclotomic_ne_zero _ _)

theorem coeff_z180K18M12NineCyclotomicProduct (r : ZMod 9) :
    z180K18M12NineCyclotomicProduct.coeff r.val = 1 := by
  rw [z180K18M12NineCyclotomicProduct_eq_geomSum, finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem r.val (Finset.mem_range.2 r.val_lt)]
  · simp
  · intro j hj hjr
    rw [coeff_X_pow, if_neg (Ne.symm hjr)]

theorem eval_one_z180K18M12NineCyclotomicProduct :
    z180K18M12NineCyclotomicProduct.eval 1 = 9 := by
  rw [z180K18M12NineCyclotomicProduct_eq_geomSum]
  simp

private theorem z180K18M12_cyclotomic_three_not_dvd_nine :
    ¬ cyclotomic 3 Int ∣ cyclotomic 9 Int := by
  intro hdiv
  have hassoc : Associated (cyclotomic 3 Int) (cyclotomic 9 Int) :=
    Irreducible.associated_of_dvd
      (cyclotomic.irreducible (by norm_num : 0 < 3))
      (cyclotomic.irreducible (by norm_num : 0 < 9)) hdiv
  have hdegree : (cyclotomic 3 Int).natDegree =
      (cyclotomic 9 Int).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_cyclotomic, natDegree_cyclotomic] at hdegree
  have htotientThree : Nat.totient 3 = 2 := by
    simpa using Nat.totient_prime (by norm_num : Nat.Prime 3)
  have htotientNine : Nat.totient 9 = 6 := by
    rw [show 9 = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num)]
    norm_num
  omega

/-- The two distinct irreducible factors combine without multiplicity. -/
theorem z180K18M12NineCyclotomicProduct_dvd
    {P : Polynomial Int}
    (h3 : cyclotomic 3 Int ∣ P) (h9 : cyclotomic 9 Int ∣ P) :
    z180K18M12NineCyclotomicProduct ∣ P := by
  obtain ⟨Q, hQ⟩ := h9
  rw [hQ] at h3 ⊢
  rcases (cyclotomic.irreducible (by norm_num : 0 < 3)).prime.dvd_mul.mp h3 with
    hbad | hdivQ
  · exact False.elim (z180K18M12_cyclotomic_three_not_dvd_nine hbad)
  · obtain ⟨R, hR⟩ := hdivQ
    refine ⟨R, ?_⟩
    simp only [z180K18M12NineCyclotomicProduct]
    rw [hR]
    ring

/-- A nonzero multiple of the degree-eight geometric sum with degree below
nine is a scalar multiple of that sum. -/
theorem eq_zero_or_eq_z180K18M12NineCyclotomicProduct_mul_C
    {P : Polynomial Int} (hdeg : P.degree < (9 : Nat))
    (hdiv : z180K18M12NineCyclotomicProduct ∣ P) :
    P = 0 ∨ ∃ c : Int, P = z180K18M12NineCyclotomicProduct * C c := by
  classical
  by_cases hP : P = 0
  · exact Or.inl hP
  · right
    let Q := Classical.choose hdiv
    have hQ : P = z180K18M12NineCyclotomicProduct * Q :=
      Classical.choose_spec hdiv
    have hQnz : Q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hQ
      exact hP hQ
    have hdegP : P.natDegree < 9 :=
      (natDegree_lt_iff_degree_lt hP).2 hdeg
    rw [hQ, natDegree_mul z180K18M12NineCyclotomicProduct_ne_zero hQnz,
      natDegree_z180K18M12NineCyclotomicProduct] at hdegP
    have hQdeg : Q.natDegree = 0 := by omega
    have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero hQdeg
    refine ⟨Q.coeff 0, ?_⟩
    calc
      P = z180K18M12NineCyclotomicProduct * Q := hQ
      _ = z180K18M12NineCyclotomicProduct * C (Q.coeff 0) :=
        congrArg (fun R : ℤ[X] => z180K18M12NineCyclotomicProduct * R) hQC

/-- `Phi_3`, `Phi_9`, and cardinality eighteen force exactly two points in
every residue class modulo nine.  This has exactly the type of the low-order
field in `Z180K18M12PairFibresExtractionInterface`. -/
theorem z180_k18_m12_nineFibres_card_two_of_phi3_phi9
    (A : Finset (ZMod 180)) (hcard : A.card = 18)
    (h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A)
    (h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A) :
    Z180K18M12NineFibresHaveCardTwo A := by
  have h3Projected :=
    cyclotomic_dvd_z180K18M12NineMask_of_dvd_mask (m := 3) (by norm_num) h3
  have h9Projected :=
    cyclotomic_dvd_z180K18M12NineMask_of_dvd_mask (m := 9) (by norm_num) h9
  have hproduct :=
    z180K18M12NineCyclotomicProduct_dvd h3Projected h9Projected
  rcases eq_zero_or_eq_z180K18M12NineCyclotomicProduct_mul_C
      (degree_z180K18M12NineMask_lt A) hproduct with
    hzero | ⟨c, hscalar⟩
  · have heval := eval_one_z180K18M12NineMask A
    norm_num [hzero, hcard] at heval
  · have heval := eval_one_z180K18M12NineMask A
    rw [hscalar, eval_mul, eval_C,
      eval_one_z180K18M12NineCyclotomicProduct, hcard] at heval
    have hc : c = 2 := by omega
    intro r
    have hcoeff := coeff_z180K18M12NineMask A r
    rw [hscalar, coeff_mul_C,
      coeff_z180K18M12NineCyclotomicProduct, hc] at hcoeff
    norm_num at hcoeff
    exact_mod_cast hcoeff.symm

#print axioms z180_k18_m12_nineFibres_card_two_of_phi3_phi9

end Fuglede
