import Fuglede.Z180ModTwoCyclotomic
import Mathlib.Tactic

/-!
# The finite-field cardinal obstruction for the `|S| = 15` case

This module specializes the polynomial part of FKMS Lemma 2.4 to
`ZMod 180 -> ZMod 45` in characteristic two.  If all five nontrivial odd
cyclotomic factors of `X^45 - 1` divide the projected mask, squarefreeness
forces that mask to be either zero or

`1 + X + ... + X^44`.

Consequently all 45 projection fibers have the same parity, and
`|S| = 45 k + 2 l`.  Combining this with the preceding characteristic-two
reduction gives the typed obstruction for the integer factors
`Phi_6, Phi_10, Phi_18, Phi_30, Phi_90`.

This is the local finite-field descent only.  The FKMS induction for the
remaining proper-subgroup branch is deliberately not asserted here.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Product of the nontrivial cyclotomic factors of `X^45 - 1` over
`F_2`. -/
noncomputable def z180K15OddCyclotomicProduct : Polynomial (ZMod 2) :=
  cyclotomic 3 (ZMod 2) * cyclotomic 5 (ZMod 2) *
  cyclotomic 9 (ZMod 2) * cyclotomic 15 (ZMod 2) *
  cyclotomic 45 (ZMod 2)

theorem z180K15OddCyclotomicProduct_mul_X_sub_one :
    z180K15OddCyclotomicProduct * (X - 1) = X ^ 45 - 1 := by
  have h := prod_cyclotomic_eq_X_pow_sub_one
    (by norm_num : 0 < 45) (ZMod 2)
  have hd : (45 : Nat).divisors = {1, 3, 5, 9, 15, 45} := by decide
  rw [hd] at h
  simpa [z180K15OddCyclotomicProduct, cyclotomic_one,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit geometric-sum form of the odd cyclotomic product. -/
theorem z180K15OddCyclotomicProduct_eq_geomSum :
    z180K15OddCyclotomicProduct =
      Finset.sum (Finset.range 45) (fun i => X ^ i) := by
  let G : Polynomial (ZMod 2) :=
    Finset.sum (Finset.range 45) (fun i => X ^ i)
  have hG : G * (X - 1) = X ^ 45 - 1 := by
    simpa [G] using (geom_sum_mul X 45)
  have hmul : (z180K15OddCyclotomicProduct - G) * (X - 1) = 0 := by
    rw [sub_mul, z180K15OddCyclotomicProduct_mul_X_sub_one,
      hG, sub_self]
  rcases mul_eq_zero.mp hmul with hzero | hbad
  · exact sub_eq_zero.mp hzero
  · exact False.elim ((X_sub_C_ne_zero (1 : ZMod 2))
      (by simpa using hbad))

theorem z180K15OddCyclotomicProduct_squarefree :
    Squarefree z180K15OddCyclotomicProduct := by
  have hc : ¬ (45 : ZMod 2) = 0 := by
    change ¬ (1 : ZMod 2) = 0
    exact one_ne_zero
  have hfull : Squarefree (X ^ 45 - 1 : Polynomial (ZMod 2)) :=
    (X_pow_sub_one_separable_iff.mpr hc).squarefree
  apply hfull.squarefree_of_dvd
  refine Dvd.intro (X - 1) ?_
  exact z180K15OddCyclotomicProduct_mul_X_sub_one

theorem natDegree_z180K15OddCyclotomicProduct :
    z180K15OddCyclotomicProduct.natDegree = 44 := by
  have h3 : cyclotomic 3 (ZMod 2) ≠ 0 := cyclotomic_ne_zero _ _
  have h5 : cyclotomic 5 (ZMod 2) ≠ 0 := cyclotomic_ne_zero _ _
  have h9 : cyclotomic 9 (ZMod 2) ≠ 0 := cyclotomic_ne_zero _ _
  have h15 : cyclotomic 15 (ZMod 2) ≠ 0 := cyclotomic_ne_zero _ _
  have h45 : cyclotomic 45 (ZMod 2) ≠ 0 := cyclotomic_ne_zero _ _
  simp only [z180K15OddCyclotomicProduct]
  rw [natDegree_mul
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h3 h5) h9) h15) h45]
  rw [natDegree_mul (mul_ne_zero (mul_ne_zero h3 h5) h9) h15]
  rw [natDegree_mul (mul_ne_zero h3 h5) h9]
  rw [natDegree_mul h3 h5]
  simp only [natDegree_cyclotomic]
  decide

theorem z180K15OddCyclotomicProduct_ne_zero :
    z180K15OddCyclotomicProduct ≠ 0 := by
  intro h
  have hh := congrArg natDegree h
  rw [natDegree_z180K15OddCyclotomicProduct, natDegree_zero] at hh
  omega

theorem coeff_z180K15OddCyclotomicProduct (i : Fin 45) :
    z180K15OddCyclotomicProduct.coeff i.val = 1 := by
  rw [z180K15OddCyclotomicProduct_eq_geomSum, finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem i.val (Finset.mem_range.2 i.isLt)]
  · simp
  · intro j hj hji
    rw [coeff_X_pow, if_neg (Ne.symm hji)]

private theorem mul_dvd_of_dvd_squarefree_super
    {a b f p : Polynomial (ZMod 2)}
    (hsq : Squarefree f) (hab : a * b ∣ f)
    (ha : a ∣ p) (hb : b ∣ p) : a * b ∣ p := by
  exact (IsRelPrime.of_squarefree_mul
    (hsq.squarefree_of_dvd hab)).mul_dvd ha hb

/-- The five individual divisibilities combine without multiplicity loss,
because their product is squarefree. -/
theorem z180K15OddCyclotomicProduct_dvd
    {P : Polynomial (ZMod 2)}
    (h3 : cyclotomic 3 (ZMod 2) ∣ P)
    (h5 : cyclotomic 5 (ZMod 2) ∣ P)
    (h9 : cyclotomic 9 (ZMod 2) ∣ P)
    (h15 : cyclotomic 15 (ZMod 2) ∣ P)
    (h45 : cyclotomic 45 (ZMod 2) ∣ P) :
    z180K15OddCyclotomicProduct ∣ P := by
  let f3 := cyclotomic 3 (ZMod 2)
  let f5 := cyclotomic 5 (ZMod 2)
  let f9 := cyclotomic 9 (ZMod 2)
  let f15 := cyclotomic 15 (ZMod 2)
  let f45 := cyclotomic 45 (ZMod 2)
  have h1545super : f15 * f45 ∣ z180K15OddCyclotomicProduct := by
    refine Dvd.intro (f3 * f5 * f9) ?_
    simp only [z180K15OddCyclotomicProduct, f3, f5, f9, f15, f45]
    ring
  have h1545 : f15 * f45 ∣ P :=
    mul_dvd_of_dvd_squarefree_super
      z180K15OddCyclotomicProduct_squarefree h1545super h15 h45
  have h91545super :
      f9 * (f15 * f45) ∣ z180K15OddCyclotomicProduct := by
    refine Dvd.intro (f3 * f5) ?_
    simp only [z180K15OddCyclotomicProduct, f3, f5, f9, f15, f45]
    ring
  have h91545 : f9 * (f15 * f45) ∣ P :=
    mul_dvd_of_dvd_squarefree_super
      z180K15OddCyclotomicProduct_squarefree h91545super h9 h1545
  have h591545super :
      f5 * (f9 * (f15 * f45)) ∣ z180K15OddCyclotomicProduct := by
    refine Dvd.intro f3 ?_
    simp only [z180K15OddCyclotomicProduct, f3, f5, f9, f15, f45]
    ring
  have h591545 : f5 * (f9 * (f15 * f45)) ∣ P :=
    mul_dvd_of_dvd_squarefree_super
      z180K15OddCyclotomicProduct_squarefree h591545super h5 h91545
  have hAllSuper :
      f3 * (f5 * (f9 * (f15 * f45))) ∣
        z180K15OddCyclotomicProduct := by
    refine Dvd.intro 1 ?_
    simp only [z180K15OddCyclotomicProduct, f3, f5, f9, f15, f45,
      mul_one]
    ring
  have hAll : f3 * (f5 * (f9 * (f15 * f45))) ∣ P :=
    mul_dvd_of_dvd_squarefree_super
      z180K15OddCyclotomicProduct_squarefree hAllSuper h3 h591545
  simpa [z180K15OddCyclotomicProduct, f3, f5, f9, f15, f45,
    mul_assoc] using hAll

/-- A multiple of the degree-44 geometric sum with degree below 45 is
either zero or the geometric sum itself. -/
theorem eq_zero_or_eq_z180K15OddCyclotomicProduct
    {P : Polynomial (ZMod 2)} (hdeg : P.degree < (45 : Nat))
    (hdiv : z180K15OddCyclotomicProduct ∣ P) :
    P = 0 ∨ P = z180K15OddCyclotomicProduct := by
  classical
  by_cases hP : P = 0
  · exact Or.inl hP
  · right
    let Q := Classical.choose hdiv
    have hQ : P = z180K15OddCyclotomicProduct * Q :=
      Classical.choose_spec hdiv
    have hQnz : Q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hQ
      exact hP hQ
    have hdegP : P.natDegree < 45 :=
      (natDegree_lt_iff_degree_lt hP).2 hdeg
    rw [hQ, natDegree_mul z180K15OddCyclotomicProduct_ne_zero hQnz,
      natDegree_z180K15OddCyclotomicProduct] at hdegP
    have hQdeg : Q.natDegree = 0 := by omega
    have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero hQdeg
    have hcoeffnz : Q.coeff 0 ≠ 0 := by
      intro hz
      apply hQnz
      rw [hQC, hz, C_0]
    have zmod_two_eq_one {q : ZMod 2} (hq : q ≠ 0) : q = 1 := by
      have hlt : q.val < 2 := q.val_lt
      interval_cases hv : q.val
      · exfalso
        apply hq
        apply ZMod.val_injective 2
        rw [ZMod.val_zero]
        exact hv
      · apply ZMod.val_injective 2
        rw [ZMod.val_one]
        exact hv
    have hcoeffone : Q.coeff 0 = 1 := zmod_two_eq_one hcoeffnz
    rw [hQC, hcoeffone, C_1, mul_one] at hQ
    exact hQ

private theorem card_eq_45_mul_add_two_mul_of_even_fibers
    (S : Finset (ZMod 180))
    (hall : ∀ i : Fin 45, 2 ∣ z180Projection45Occupancy S i) :
    ∃ k l : Nat, S.card = k * 45 + l * 2 := by
  classical
  have hex : ∀ i : Fin 45, ∃ q : Nat,
      z180Projection45Occupancy S i = 2 * q := by
    intro i
    let q := Classical.choose (hall i)
    have hq := Classical.choose_spec (hall i)
    exact ⟨q, hq⟩
  choose q hq using hex
  refine ⟨0, Finset.univ.sum q, ?_⟩
  rw [zero_mul, zero_add]
  rw [show S.card =
    Finset.univ.sum (fun i : Fin 45 => z180Projection45Occupancy S i)
      from (sum_z180Projection45Occupancy S).symm]
  simp_rw [hq]
  have hmul : 2 * Finset.univ.sum q =
      Finset.univ.sum (fun i => 2 * q i) := by
    simpa using (Finset.mul_sum (Finset.univ : Finset (Fin 45)) q 2)
  rw [show Finset.univ.sum (fun i => 2 * q i) =
    2 * Finset.univ.sum q from hmul.symm]
  omega

private theorem card_eq_45_mul_add_two_mul_of_odd_fibers
    (S : Finset (ZMod 180))
    (hall : ∀ i : Fin 45,
      (z180Projection45Occupancy S i : ZMod 2) = 1) :
    ∃ k l : Nat, S.card = k * 45 + l * 2 := by
  classical
  have hex : ∀ i : Fin 45, ∃ q : Nat,
      z180Projection45Occupancy S i = 2 * q + 1 := by
    intro i
    have hv : z180Projection45Occupancy S i % 2 = 1 := by
      have hh := congrArg ZMod.val (hall i)
      rw [ZMod.val_natCast, ZMod.val_one] at hh
      exact hh
    refine ⟨z180Projection45Occupancy S i / 2, ?_⟩
    have hdecomp := Nat.mod_add_div (z180Projection45Occupancy S i) 2
    omega
  choose q hq using hex
  refine ⟨1, Finset.univ.sum q, ?_⟩
  rw [one_mul]
  rw [show S.card =
    Finset.univ.sum (fun i : Fin 45 => z180Projection45Occupancy S i)
      from (sum_z180Projection45Occupancy S).symm]
  simp_rw [hq]
  rw [Finset.sum_add_distrib]
  have hmul : 2 * Finset.univ.sum q =
      Finset.univ.sum (fun i => 2 * q i) := by
    simpa using (Finset.mul_sum (Finset.univ : Finset (Fin 45)) q 2)
  rw [show Finset.univ.sum (fun i => 2 * q i) =
    2 * Finset.univ.sum q from hmul.symm]
  simp
  omega

/-- Specialized FKMS Lemma 2.4: the five nontrivial odd factors force the
cardinality into `45 Nat + 2 Nat`. -/
theorem z180_card_eq_45_mul_add_two_mul_of_projection45_cyclotomic_divisors
    (S : Finset (ZMod 180))
    (h3 : cyclotomic 3 (ZMod 2) ∣ z180Projection45MaskModTwo S)
    (h5 : cyclotomic 5 (ZMod 2) ∣ z180Projection45MaskModTwo S)
    (h9 : cyclotomic 9 (ZMod 2) ∣ z180Projection45MaskModTwo S)
    (h15 : cyclotomic 15 (ZMod 2) ∣ z180Projection45MaskModTwo S)
    (h45 : cyclotomic 45 (ZMod 2) ∣ z180Projection45MaskModTwo S) :
    ∃ k l : Nat, S.card = k * 45 + l * 2 := by
  have hdiv := z180K15OddCyclotomicProduct_dvd h3 h5 h9 h15 h45
  rcases eq_zero_or_eq_z180K15OddCyclotomicProduct
      (degree_z180Projection45MaskModTwo_lt S) hdiv with hzero | hgeom
  · apply card_eq_45_mul_add_two_mul_of_even_fibers S
    intro i
    have hcoeff := coeff_z180Projection45MaskModTwo S i
    rw [hzero, coeff_zero] at hcoeff
    exact (ZMod.natCast_eq_zero_iff
      (z180Projection45Occupancy S i) 2).mp hcoeff.symm
  · apply card_eq_45_mul_add_two_mul_of_odd_fibers S
    intro i
    have hcoeff := coeff_z180Projection45MaskModTwo S i
    rw [hgeom, coeff_z180K15OddCyclotomicProduct] at hcoeff
    exact hcoeff.symm

/-- Fully typed specialization of FKMS Lemmas 2.3 and 2.4 for the five
even indices above the divisors `3,5,9,15,45` of 45. -/
theorem z180_card_eq_45_mul_add_two_mul_of_even_index_cyclotomic_divisors
    (S : Finset (ZMod 180))
    (h6 : cyclotomic 6 Int ∣ maskPolynomial 180 S)
    (h10 : cyclotomic 10 Int ∣ maskPolynomial 180 S)
    (h18 : cyclotomic 18 Int ∣ maskPolynomial 180 S)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 S)
    (h90 : cyclotomic 90 Int ∣ maskPolynomial 180 S) :
    ∃ k l : Nat, S.card = k * 45 + l * 2 := by
  apply z180_card_eq_45_mul_add_two_mul_of_projection45_cyclotomic_divisors S
  · exact cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 3) (by norm_num) (by norm_num) (by simpa using h6)
  · exact cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 5) (by norm_num) (by norm_num) (by simpa using h10)
  · exact cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 9) (by norm_num) (by norm_num) (by simpa using h18)
  · exact cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 15) (by norm_num) (by norm_num) (by simpa using h30)
  · exact cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 45) (by norm_num) (by norm_num) (by simpa using h90)

/-- At cardinality 15 the five even-index divisibilities cannot all hold.
This is the exact local obstruction; it does not choose or close the
remaining subgroup-induction branch. -/
theorem z180_k15_not_all_even_index_cyclotomic_divisors
    {S : Finset (ZMod 180)} (hcard : S.card = 15) :
    ¬ (cyclotomic 6 Int ∣ maskPolynomial 180 S ∧
      cyclotomic 10 Int ∣ maskPolynomial 180 S ∧
      cyclotomic 18 Int ∣ maskPolynomial 180 S ∧
      cyclotomic 30 Int ∣ maskPolynomial 180 S ∧
      cyclotomic 90 Int ∣ maskPolynomial 180 S) := by
  rintro ⟨h6, h10, h18, h30, h90⟩
  obtain ⟨k, l, hkl⟩ :=
    z180_card_eq_45_mul_add_two_mul_of_even_index_cyclotomic_divisors
      S h6 h10 h18 h30 h90
  omega

#print axioms z180_card_eq_45_mul_add_two_mul_of_projection45_cyclotomic_divisors
#print axioms z180_card_eq_45_mul_add_two_mul_of_even_index_cyclotomic_divisors
#print axioms z180_k15_not_all_even_index_cyclotomic_divisors

end Fuglede
