import Fuglede.Z180K10ModThreeBridge
import Mathlib.Tactic

/-!
# The `F_3` geometric-sum obstruction at cardinality ten

The five nontrivial cyclotomic factors of `X^20 - 1` have product
`1 + X + ... + X^19`.  If they all divide a projected zero-one mask of
degree below twenty, that mask is a scalar multiple of this geometric sum.
Its value at one forces the scalar to be two in `F_3`, contradicting a
coefficient belonging to an occupied projection fibre.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Product of all nontrivial cyclotomic factors of `X^20 - 1` over `F_3`. -/
noncomputable def z180K10CyclotomicProductModThree :
    Polynomial (ZMod 3) :=
  cyclotomic 2 (ZMod 3) * cyclotomic 4 (ZMod 3) *
    cyclotomic 5 (ZMod 3) * cyclotomic 10 (ZMod 3) *
    cyclotomic 20 (ZMod 3)

theorem z180K10CyclotomicProductModThree_mul_X_sub_one :
    z180K10CyclotomicProductModThree * (X - 1) = X ^ 20 - 1 := by
  have h := prod_cyclotomic_eq_X_pow_sub_one
    (by norm_num : 0 < 20) (ZMod 3)
  have hd : (20 : Nat).divisors = {1, 2, 4, 5, 10, 20} := by
    decide
  rw [hd] at h
  simpa [z180K10CyclotomicProductModThree, cyclotomic_one,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit geometric-sum form of the product. -/
theorem z180K10CyclotomicProductModThree_eq_geomSum :
    z180K10CyclotomicProductModThree =
      Finset.sum (Finset.range 20) (fun i => X ^ i) := by
  let G : Polynomial (ZMod 3) :=
    Finset.sum (Finset.range 20) (fun i => X ^ i)
  have hG : G * (X - 1) = X ^ 20 - 1 := by
    simpa [G] using (geom_sum_mul X 20)
  have hmul :
      (z180K10CyclotomicProductModThree - G) * (X - 1) = 0 := by
    rw [sub_mul, z180K10CyclotomicProductModThree_mul_X_sub_one,
      hG, sub_self]
  rcases mul_eq_zero.mp hmul with hzero | hbad
  · exact sub_eq_zero.mp hzero
  · exact False.elim ((X_sub_C_ne_zero (1 : ZMod 3))
      (by simpa using hbad))

theorem z180K10CyclotomicProductModThree_squarefree :
    Squarefree z180K10CyclotomicProductModThree := by
  have hc : ¬ (20 : ZMod 3) = 0 := by decide
  have hfull : Squarefree (X ^ 20 - 1 : Polynomial (ZMod 3)) :=
    (X_pow_sub_one_separable_iff.mpr hc).squarefree
  apply hfull.squarefree_of_dvd
  refine Dvd.intro (X - 1) ?_
  exact z180K10CyclotomicProductModThree_mul_X_sub_one

theorem natDegree_z180K10CyclotomicProductModThree :
    z180K10CyclotomicProductModThree.natDegree = 19 := by
  have h2 : cyclotomic 2 (ZMod 3) ≠ 0 := cyclotomic_ne_zero _ _
  have h4 : cyclotomic 4 (ZMod 3) ≠ 0 := cyclotomic_ne_zero _ _
  have h5 : cyclotomic 5 (ZMod 3) ≠ 0 := cyclotomic_ne_zero _ _
  have h10 : cyclotomic 10 (ZMod 3) ≠ 0 := cyclotomic_ne_zero _ _
  have h20 : cyclotomic 20 (ZMod 3) ≠ 0 := cyclotomic_ne_zero _ _
  simp only [z180K10CyclotomicProductModThree]
  rw [natDegree_mul
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h4) h5) h10) h20]
  rw [natDegree_mul (mul_ne_zero (mul_ne_zero h2 h4) h5) h10]
  rw [natDegree_mul (mul_ne_zero h2 h4) h5]
  rw [natDegree_mul h2 h4]
  simp only [natDegree_cyclotomic]
  decide

theorem z180K10CyclotomicProductModThree_ne_zero :
    z180K10CyclotomicProductModThree ≠ 0 := by
  intro h
  have hh := congrArg natDegree h
  rw [natDegree_z180K10CyclotomicProductModThree, natDegree_zero] at hh
  omega

theorem coeff_z180K10CyclotomicProductModThree (i : Fin 20) :
    z180K10CyclotomicProductModThree.coeff i.val = 1 := by
  rw [z180K10CyclotomicProductModThree_eq_geomSum, finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem i.val (Finset.mem_range.2 i.isLt)]
  · simp
  · intro j hj hji
    rw [coeff_X_pow, if_neg (Ne.symm hji)]

theorem eval_one_z180K10CyclotomicProductModThree :
    z180K10CyclotomicProductModThree.eval 1 = (20 : ZMod 3) := by
  rw [z180K10CyclotomicProductModThree_eq_geomSum]
  simp

private theorem mul_dvd_of_dvd_squarefree_super_mod_three
    {a b f p : Polynomial (ZMod 3)}
    (hsq : Squarefree f) (hab : a * b ∣ f)
    (ha : a ∣ p) (hb : b ∣ p) : a * b ∣ p := by
  exact (IsRelPrime.of_squarefree_mul
    (hsq.squarefree_of_dvd hab)).mul_dvd ha hb

/-- Squarefreeness combines the five individual divisibilities without
multiplicity loss. -/
theorem z180K10CyclotomicProductModThree_dvd
    {P : Polynomial (ZMod 3)}
    (h2 : cyclotomic 2 (ZMod 3) ∣ P)
    (h4 : cyclotomic 4 (ZMod 3) ∣ P)
    (h5 : cyclotomic 5 (ZMod 3) ∣ P)
    (h10 : cyclotomic 10 (ZMod 3) ∣ P)
    (h20 : cyclotomic 20 (ZMod 3) ∣ P) :
    z180K10CyclotomicProductModThree ∣ P := by
  let f2 := cyclotomic 2 (ZMod 3)
  let f4 := cyclotomic 4 (ZMod 3)
  let f5 := cyclotomic 5 (ZMod 3)
  let f10 := cyclotomic 10 (ZMod 3)
  let f20 := cyclotomic 20 (ZMod 3)
  have h1020super : f10 * f20 ∣ z180K10CyclotomicProductModThree := by
    refine Dvd.intro (f2 * f4 * f5) ?_
    simp only [z180K10CyclotomicProductModThree,
      f2, f4, f5, f10, f20]
    ring
  have h1020 : f10 * f20 ∣ P :=
    mul_dvd_of_dvd_squarefree_super_mod_three
      z180K10CyclotomicProductModThree_squarefree h1020super h10 h20
  have h51020super :
      f5 * (f10 * f20) ∣ z180K10CyclotomicProductModThree := by
    refine Dvd.intro (f2 * f4) ?_
    simp only [z180K10CyclotomicProductModThree,
      f2, f4, f5, f10, f20]
    ring
  have h51020 : f5 * (f10 * f20) ∣ P :=
    mul_dvd_of_dvd_squarefree_super_mod_three
      z180K10CyclotomicProductModThree_squarefree h51020super h5 h1020
  have h451020super :
      f4 * (f5 * (f10 * f20)) ∣
        z180K10CyclotomicProductModThree := by
    refine Dvd.intro f2 ?_
    simp only [z180K10CyclotomicProductModThree,
      f2, f4, f5, f10, f20]
    ring
  have h451020 : f4 * (f5 * (f10 * f20)) ∣ P :=
    mul_dvd_of_dvd_squarefree_super_mod_three
      z180K10CyclotomicProductModThree_squarefree
      h451020super h4 h51020
  have hAllSuper :
      f2 * (f4 * (f5 * (f10 * f20))) ∣
        z180K10CyclotomicProductModThree := by
    refine Dvd.intro 1 ?_
    simp only [z180K10CyclotomicProductModThree,
      f2, f4, f5, f10, f20, mul_one]
    ring
  have hAll : f2 * (f4 * (f5 * (f10 * f20))) ∣ P :=
    mul_dvd_of_dvd_squarefree_super_mod_three
      z180K10CyclotomicProductModThree_squarefree
      hAllSuper h2 h451020
  simpa [z180K10CyclotomicProductModThree,
    f2, f4, f5, f10, f20, mul_assoc] using hAll

/-- A multiple of the degree-nineteen geometric sum with degree below
twenty is zero or a scalar multiple of that sum. -/
theorem eq_zero_or_eq_z180K10CyclotomicProductModThree_mul_C
    {P : Polynomial (ZMod 3)} (hdeg : P.degree < (20 : Nat))
    (hdiv : z180K10CyclotomicProductModThree ∣ P) :
    P = 0 ∨ ∃ c : ZMod 3,
      P = z180K10CyclotomicProductModThree * C c := by
  classical
  by_cases hP : P = 0
  · exact Or.inl hP
  · right
    let Q := Classical.choose hdiv
    have hQ : P = z180K10CyclotomicProductModThree * Q :=
      Classical.choose_spec hdiv
    have hQnz : Q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hQ
      exact hP hQ
    have hdegP : P.natDegree < 20 :=
      (natDegree_lt_iff_degree_lt hP).2 hdeg
    rw [hQ, natDegree_mul z180K10CyclotomicProductModThree_ne_zero hQnz,
      natDegree_z180K10CyclotomicProductModThree] at hdegP
    have hQdeg : Q.natDegree = 0 := by omega
    have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero hQdeg
    refine ⟨Q.coeff 0, ?_⟩
    rw [hQ, hQC]
    simp only [coeff_C_zero]

private theorem zmod_three_eq_two_of_two_mul_eq_one
    (c : ZMod 3) (h : (2 : ZMod 3) * c = 1) : c = 2 := by
  revert c
  decide

/-- A cardinality-ten set injective modulo twenty cannot have all five
nontrivial projected cyclotomic factors. -/
theorem z180_k10_not_all_projection20_factors
    {S : Finset (ZMod 180)} (hcard : S.card = 10)
    (hinj : Set.InjOn z180K10Projection20 (S : Set (ZMod 180))) :
    ¬ ((cyclotomic 2 (ZMod 3) ∣ z180Projection20MaskModThree S) ∧
      (cyclotomic 4 (ZMod 3) ∣ z180Projection20MaskModThree S) ∧
      (cyclotomic 5 (ZMod 3) ∣ z180Projection20MaskModThree S) ∧
      (cyclotomic 10 (ZMod 3) ∣ z180Projection20MaskModThree S) ∧
      (cyclotomic 20 (ZMod 3) ∣ z180Projection20MaskModThree S)) := by
  rintro ⟨h2, h4, h5, h10, h20⟩
  have hproduct :=
    z180K10CyclotomicProductModThree_dvd h2 h4 h5 h10 h20
  rcases eq_zero_or_eq_z180K10CyclotomicProductModThree_mul_C
      (degree_z180Projection20MaskModThree_lt S) hproduct with
    hzero | ⟨c, hscalar⟩
  · have heval := eval_one_z180Projection20MaskModThree S
    norm_num [hzero, hcard] at heval
    exact (by decide : (0 : ZMod 3) ≠ 10) heval
  · have heval := eval_one_z180Projection20MaskModThree S
    rw [hscalar, eval_mul, eval_C,
      eval_one_z180K10CyclotomicProductModThree, hcard] at heval
    have hc : c = 2 := by
      apply zmod_three_eq_two_of_two_mul_eq_one
      norm_num at heval ⊢
      exact heval
    have hSpos : 0 < S.card := by
      rw [hcard]
      norm_num
    have hnonempty : S.Nonempty := Finset.card_pos.mp hSpos
    obtain ⟨x, hx⟩ := hnonempty
    let i := z180Projection20Coordinate x
    have hpos : 0 < z180Projection20Occupancy S i := by
      apply Finset.card_pos.mpr
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    have hle := z180Projection20Occupancy_le_one_of_injOn hinj i
    have hi : z180Projection20Occupancy S i = 1 := by omega
    have hcoeff := coeff_z180Projection20MaskModThree S i
    rw [hscalar, coeff_mul_C,
      coeff_z180K10CyclotomicProductModThree, hc, hi] at hcoeff
    norm_num at hcoeff
    exact (by decide : (2 : ZMod 3) ≠ 1) hcoeff

#print axioms z180_k10_not_all_projection20_factors

end Fuglede
