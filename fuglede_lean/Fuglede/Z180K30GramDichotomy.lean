import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# The scalar core of the K30 five-Gram dichotomy

This file isolates the finite algebra which remains after simultaneously
diagonalising the five positive Hermitian `6 x 6` column-Gram operators.

For one common eigenvector, write its five (real) eigenvalues as `lambda r`.
The block identities give

* `sum_r lambda r = 30`, and
* all products `lambda r * lambda s`, for `r != s`, have one common value.

The first theorem below proves that such a five-tuple is either constantly
`6`, or is `30` in one position and `0` in the other four positions.  Across
the six common eigenvectors, trace `36` gives

`6 * uniformMultiplicity + 30 * spikeMultiplicity r = 36`.

Consequently either all six coordinates are uniform, or there is one common
uniform coordinate and one private spike coordinate for each of the five
operators.  In the second case every Gram operator has eigenvalues
`30, 6, 0, 0, 0, 0`, hence rank two.

The matrix-to-joint-spectrum step is deliberately not asserted here.  The
relevant Mathlib endpoint is
`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` (and its internal-direct-
sum companion) from `Mathlib.Analysis.InnerProductSpace.JointEigenspace`.
The trace and positivity endpoints are respectively
`LinearMap.IsSymmetric.trace_eq_sum_eigenvalues` and
`LinearMap.IsPositive.nonneg_eigenvalues`.
-/

namespace Fuglede

open scoped BigOperators

/-- The normal scalar pattern on one common eigendirection. -/
def Z180K30GramNormalScalar (lambda : Fin 5 -> Real) : Prop :=
  forall r, lambda r = 6

/-- The scalar spike with owner `r`: eigenvalue `30` for `r`, and zero for
the other four Gram operators. -/
def Z180K30GramSpikeAt (lambda : Fin 5 -> Real) (r : Fin 5) : Prop :=
  lambda r = 30 /\ forall s, s != r -> lambda s = 0

/-- The exceptional scalar pattern on one common eigendirection. -/
def Z180K30GramSpikeScalar (lambda : Fin 5 -> Real) : Prop :=
  exists r, Z180K30GramSpikeAt lambda r

private theorem finFive_exists_ne_and_ne (i j : Fin 5) :
    exists k : Fin 5, k != i /\ k != j := by
  fin_cases i <;> fin_cases j <;> decide

/-- Scalar K30 Gram dichotomy.

Positivity is not needed at this stage: the common off-diagonal product and
the positive total sum already force the stated alternatives.  Positivity is
still recorded in the joint-spectrum package below because it is the natural
output of positive-semidefiniteness. -/
theorem z180K30_five_scalar_gram_dichotomy
    (lambda : Fin 5 -> Real)
    (hsum : (sum r, lambda r) = 30)
    (hcross : exists q : Real,
      forall r s, r != s -> lambda r * lambda s = q) :
    Z180K30GramNormalScalar lambda \/ Z180K30GramSpikeScalar lambda := by
  rcases hcross with ⟨q, hq⟩
  by_cases hqzero : q = 0
  · have hexists : exists r, lambda r != 0 := by
      by_contra hallzero
      push_neg at hallzero
      have hzero : (sum r, lambda r) = 0 := by simp [hallzero]
      linarith
    rcases hexists with ⟨owner, howner⟩
    right
    refine ⟨owner, ?_, ?_⟩
    · have hsumSingle : (sum r, lambda r) = lambda owner := by
        rw [Fintype.sum_eq_single owner]
        intro s hs
        have hproduct := hq owner s hs.symm
        rw [hqzero] at hproduct
        exact (mul_eq_zero.mp hproduct).resolve_left howner
      linarith
    · intro s hs
      have hproduct := hq owner s hs.symm
      rw [hqzero] at hproduct
      exact (mul_eq_zero.mp hproduct).resolve_left howner
  · left
    have hnonzero : forall i, lambda i != 0 := by
      intro i hi
      obtain ⟨j, hji, _⟩ := finFive_exists_ne_and_ne i i
      have hproduct := hq i j hji.symm
      rw [hi, zero_mul] at hproduct
      exact hqzero hproduct.symm
    have hequal : forall i j, lambda i = lambda j := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := finFive_exists_ne_and_ne i j
      have hik := hq i k hki.symm
      have hjk := hq j k hkj.symm
      exact mul_right_cancel₀ (hnonzero k) (hik.trans hjk.symm)
    intro i
    have hsumConst : (sum j, lambda j) = (sum _j : Fin 5, lambda i) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hequal j i
    have hfive : (sum _j : Fin 5, lambda i) = 5 * lambda i := by
      norm_num
    linarith

/-- A normal scalar pattern and a spike pattern cannot occur simultaneously. -/
theorem Z180K30GramNormalScalar.not_spikeAt
    {lambda : Fin 5 -> Real} (hnormal : Z180K30GramNormalScalar lambda)
    (r : Fin 5) : not (Z180K30GramSpikeAt lambda r) := by
  intro hspike
  have hsix := hnormal r
  have hthirty := hspike.1
  linarith

/-- Indicator form of the scalar dichotomy.  This is the form used to turn
trace sums into multiplicity equations. -/
theorem z180K30_scalar_value_eq_normal_add_spike_indicator
    {lambda : Fin 5 -> Real}
    (hpattern : Z180K30GramNormalScalar lambda \/
      Z180K30GramSpikeScalar lambda)
    (r : Fin 5) :
    lambda r =
      (if Z180K30GramNormalScalar lambda then 6 else 0) +
      (if Z180K30GramSpikeAt lambda r then 30 else 0) := by
  classical
  rcases hpattern with hnormal | ⟨owner, howner⟩
  · have hnspike := hnormal.not_spikeAt r
    simp [hnormal, hnspike, hnormal r]
  · have hnnormal : not (Z180K30GramNormalScalar lambda) := by
      intro hnormal
      exact (hnormal.not_spikeAt owner) howner
    by_cases hor : owner = r
    · subst owner
      simp [hnnormal, howner, howner.1]
    · have hzero : lambda r = 0 := howner.2 r hor.symm
      have hnspike : not (Z180K30GramSpikeAt lambda r) := by
        intro hspike
        linarith [hspike.1]
      simp [hnnormal, hnspike, hzero]

/-- Number of common eigencoordinates carrying the uniform `(6,6,6,6,6)`
pattern. -/
noncomputable def z180K30GramUniformMultiplicity
    (lambda : Fin 6 -> Fin 5 -> Real) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin 6)).filter fun k =>
    Z180K30GramNormalScalar (lambda k)).card

/-- Number of common eigencoordinates carrying the spike owned by `r`. -/
noncomputable def z180K30GramSpikeMultiplicity
    (lambda : Fin 6 -> Fin 5 -> Real) (r : Fin 5) : Nat := by
  classical
  exact ((Finset.univ : Finset (Fin 6)).filter fun k =>
    Z180K30GramSpikeAt (lambda k) r).card

private theorem sum_indicator_eq_card_filter_mul
    {alpha : Type*} [Fintype alpha]
    (p : alpha -> Prop) [DecidablePred p] (c : Real) :
    (sum i, if p i then c else 0) =
      (((Finset.univ.filter p).card : Nat) : Real) * c := by
  calc
    (sum i, if p i then c else 0) =
        (sum i, if p i then (1 : Real) else 0) * c := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hpi : p i <;> simp [hpi]
    _ = (((Finset.univ.filter p).card : Nat) : Real) * c := by
          rw [Finset.sum_boole]

/-- Trace `36`, after the scalar dichotomy, is exactly the integral
multiplicity equation `6 u + 30 n_r = 36`. -/
theorem z180K30_trace_eq_multiplicity_equation
    (lambda : Fin 6 -> Fin 5 -> Real)
    (hpattern : forall k,
      Z180K30GramNormalScalar (lambda k) \/
        Z180K30GramSpikeScalar (lambda k))
    (htrace : forall r, (sum k, lambda k r) = 36) :
    forall r,
      6 * z180K30GramUniformMultiplicity lambda +
        30 * z180K30GramSpikeMultiplicity lambda r = 36 := by
  classical
  intro r
  have hdecompose :
      (sum k, lambda k r) =
        (sum k,
          if Z180K30GramNormalScalar (lambda k) then (6 : Real) else 0) +
        (sum k,
          if Z180K30GramSpikeAt (lambda k) r then (30 : Real) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    exact z180K30_scalar_value_eq_normal_add_spike_indicator (hpattern k) r
  have huniform :
      (sum k,
        if Z180K30GramNormalScalar (lambda k) then (6 : Real) else 0) =
        (z180K30GramUniformMultiplicity lambda : Real) * 6 := by
    simpa [z180K30GramUniformMultiplicity] using
      (sum_indicator_eq_card_filter_mul
        (fun k : Fin 6 => Z180K30GramNormalScalar (lambda k)) 6)
  have hspike :
      (sum k,
        if Z180K30GramSpikeAt (lambda k) r then (30 : Real) else 0) =
        (z180K30GramSpikeMultiplicity lambda r : Real) * 30 := by
    simpa [z180K30GramSpikeMultiplicity] using
      (sum_indicator_eq_card_filter_mul
        (fun k : Fin 6 => Z180K30GramSpikeAt (lambda k) r) 30)
  have hreal :
      (z180K30GramUniformMultiplicity lambda : Real) * 6 +
        (z180K30GramSpikeMultiplicity lambda r : Real) * 30 = 36 := by
    rw [← huniform, ← hspike, ← hdecompose, htrace r]
  have hnat :
      z180K30GramUniformMultiplicity lambda * 6 +
        z180K30GramSpikeMultiplicity lambda r * 30 = 36 := by
    exact_mod_cast hreal
  simpa [Nat.mul_comm] using hnat

/-- The two and only two solutions of the six-dimensional trace equations. -/
theorem z180K30_trace_multiplicity_dichotomy
    (uniform : Nat) (spike : Fin 5 -> Nat)
    (htrace : forall r, 6 * uniform + 30 * spike r = 36) :
    (uniform = 6 /\ forall r, spike r = 0) \/
      (uniform = 1 /\ forall r, spike r = 1) := by
  have hzero := htrace (0 : Fin 5)
  have huniform : uniform = 6 \/ uniform = 1 := by omega
  rcases huniform with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    intro r
    have hr := htrace r
    omega
  · right
    refine ⟨rfl, ?_⟩
    intro r
    have hr := htrace r
    omega

/-- Lean-friendly output of the analytic simultaneous-diagonalisation step.

`eigenvalue k r` is the eigenvalue of Gram operator `r` on common
eigencoordinate `k`.  The fields are direct scalar consequences of:

* positivity of each Gram operator;
* sum of the five Gram operators equal to `30 I`;
* equality of all cross-products on distinct indices; and
* trace `36` for each operator.

Keeping this package explicit prevents the still-unformalised construction of
a common eigenbasis from being silently assumed. -/
structure Z180K30GramJointEigenvalueData where
  eigenvalue : Fin 6 -> Fin 5 -> Real
  nonnegative : forall k r, 0 <= eigenvalue k r
  sum_eq_thirty : forall k, (sum r, eigenvalue k r) = 30
  common_cross_product : forall k, exists q : Real,
    forall r s, r != s -> eigenvalue k r * eigenvalue k s = q
  trace_eq_thirtySix : forall r, (sum k, eigenvalue k r) = 36

/-- The exceptional spectral shape.  Together with `coordinatePattern`, the
multiplicity fields say exactly that every operator has one eigenvalue `30`,
the same common eigenvalue `6`, and four zero eigenvalues. -/
structure Z180K30ExceptionalGramEigenvalueData
    (lambda : Fin 6 -> Fin 5 -> Real) : Prop where
  coordinatePattern : forall k,
    Z180K30GramNormalScalar (lambda k) \/
      Z180K30GramSpikeScalar (lambda k)
  oneUniform : z180K30GramUniformMultiplicity lambda = 1
  oneSpikeEach : forall r, z180K30GramSpikeMultiplicity lambda r = 1

theorem Z180K30GramJointEigenvalueData.coordinatePattern
    (data : Z180K30GramJointEigenvalueData) (k : Fin 6) :
    Z180K30GramNormalScalar (data.eigenvalue k) \/
      Z180K30GramSpikeScalar (data.eigenvalue k) :=
  z180K30_five_scalar_gram_dichotomy
    (data.eigenvalue k) (data.sum_eq_thirty k)
      (data.common_cross_product k)

theorem Z180K30GramJointEigenvalueData.multiplicityEquation
    (data : Z180K30GramJointEigenvalueData) :
    forall r,
      6 * z180K30GramUniformMultiplicity data.eigenvalue +
        30 * z180K30GramSpikeMultiplicity data.eigenvalue r = 36 :=
  z180K30_trace_eq_multiplicity_equation data.eigenvalue
    data.coordinatePattern data.trace_eq_thirtySix

/-- Central K30 five-Gram dichotomy at the joint-eigenvalue boundary.

The left branch says all six joint eigencoordinates have eigenvalue `6` for
all five operators, which is equivalent to every Gram operator being `6 I`
once the common eigenbasis is supplied.  The right branch is the rank-two
`(30,6,0,0,0,0)` alternative. -/
theorem Z180K30GramJointEigenvalueData.dichotomy
    (data : Z180K30GramJointEigenvalueData) :
    (forall k, Z180K30GramNormalScalar (data.eigenvalue k)) \/
      Z180K30ExceptionalGramEigenvalueData data.eigenvalue := by
  classical
  rcases z180K30_trace_multiplicity_dichotomy
      (z180K30GramUniformMultiplicity data.eigenvalue)
      (z180K30GramSpikeMultiplicity data.eigenvalue)
      data.multiplicityEquation with hnormal | hexceptional
  · left
    intro k
    have hcard :
        ((Finset.univ : Finset (Fin 6)).filter fun j =>
          Z180K30GramNormalScalar (data.eigenvalue j)).card =
          (Finset.univ : Finset (Fin 6)).card := by
      simpa [z180K30GramUniformMultiplicity] using hnormal.1
    exact (Finset.card_filter_eq_iff.mp hcard) k (by simp)
  · right
    exact
      { coordinatePattern := data.coordinatePattern
        oneUniform := hexceptional.1
        oneSpikeEach := hexceptional.2 }

end Fuglede
