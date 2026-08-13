import Fuglede.Z180K30GramScalarDichotomy

/-!
# Joint-eigenvalue boundary for the K30 Gram dichotomy

The input structure below is exactly the scalar data supplied by a common
eigenbasis.  This module derives the normal/rank-two alternative, but does
not assert that Fourier-block Gram operators admit such data.
-/

namespace Fuglede

open scoped BigOperators

theorem Z180K30GramNormalScalar.not_spikeAt
    {lambda : Fin 5 → ℝ} (hnormal : Z180K30GramNormalScalar lambda)
    (r : Fin 5) : ¬ Z180K30GramSpikeAt lambda r := by
  intro hspike
  have hsix := hnormal r
  have hthirty := hspike.1
  linarith

theorem z180K30_scalar_value_eq_normal_add_spike_indicator
    {lambda : Fin 5 → ℝ}
    (hpattern : Z180K30GramNormalScalar lambda ∨
      Z180K30GramSpikeScalar lambda)
    (r : Fin 5) :
    lambda r =
      (if Z180K30GramNormalScalar lambda then 6 else 0) +
      (if Z180K30GramSpikeAt lambda r then 30 else 0) := by
  classical
  rcases hpattern with hnormal | ⟨owner, howner⟩
  · have hnspike := hnormal.not_spikeAt r
    simp [hnormal, hnspike, hnormal r]
  · have hnnormal : ¬ Z180K30GramNormalScalar lambda := by
      intro hnormal
      exact (hnormal.not_spikeAt owner) howner
    by_cases hor : owner = r
    · subst owner
      simp [hnnormal, howner, howner.1]
    · have hzero : lambda r = 0 := howner.2 r hor.symm
      have hnspike : ¬ Z180K30GramSpikeAt lambda r := by
        intro hspike
        linarith [hspike.1]
      simp [hnnormal, hnspike, hzero]

noncomputable def z180K30GramUniformMultiplicity
    (lambda : Fin 6 → Fin 5 → ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin 6)).filter fun k =>
    Z180K30GramNormalScalar (lambda k)).card

noncomputable def z180K30GramSpikeMultiplicity
    (lambda : Fin 6 → Fin 5 → ℝ) (r : Fin 5) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin 6)).filter fun k =>
    Z180K30GramSpikeAt (lambda k) r).card

private theorem sum_indicator_eq_card_filter_mul
    {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (∑ i, if p i then c else 0) =
      (((Finset.univ.filter p).card : ℕ) : ℝ) * c := by
  calc
    (∑ i, if p i then c else 0) =
        (∑ i, if p i then (1 : ℝ) else 0) * c := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hpi : p i <;> simp [hpi]
    _ = (((Finset.univ.filter p).card : ℕ) : ℝ) * c := by
          rw [Finset.sum_boole]

theorem z180K30_trace_eq_multiplicity_equation
    (lambda : Fin 6 → Fin 5 → ℝ)
    (hpattern : ∀ k,
      Z180K30GramNormalScalar (lambda k) ∨
        Z180K30GramSpikeScalar (lambda k))
    (htrace : ∀ r, (∑ k, lambda k r) = 36) :
    ∀ r,
      6 * z180K30GramUniformMultiplicity lambda +
        30 * z180K30GramSpikeMultiplicity lambda r = 36 := by
  classical
  intro r
  have hdecompose :
      (∑ k, lambda k r) =
        (∑ k,
          if Z180K30GramNormalScalar (lambda k) then (6 : ℝ) else 0) +
        (∑ k,
          if Z180K30GramSpikeAt (lambda k) r then (30 : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    exact z180K30_scalar_value_eq_normal_add_spike_indicator
      (hpattern k) r
  have huniform :
      (∑ k,
        if Z180K30GramNormalScalar (lambda k) then (6 : ℝ) else 0) =
        (z180K30GramUniformMultiplicity lambda : ℝ) * 6 := by
    simpa [z180K30GramUniformMultiplicity] using
      (sum_indicator_eq_card_filter_mul
        (fun k : Fin 6 => Z180K30GramNormalScalar (lambda k)) 6)
  have hspike :
      (∑ k,
        if Z180K30GramSpikeAt (lambda k) r then (30 : ℝ) else 0) =
        (z180K30GramSpikeMultiplicity lambda r : ℝ) * 30 := by
    simpa [z180K30GramSpikeMultiplicity] using
      (sum_indicator_eq_card_filter_mul
        (fun k : Fin 6 => Z180K30GramSpikeAt (lambda k) r) 30)
  have hreal :
      (z180K30GramUniformMultiplicity lambda : ℝ) * 6 +
        (z180K30GramSpikeMultiplicity lambda r : ℝ) * 30 = 36 := by
    rw [← huniform, ← hspike, ← hdecompose, htrace r]
  have hnat :
      z180K30GramUniformMultiplicity lambda * 6 +
        z180K30GramSpikeMultiplicity lambda r * 30 = 36 := by
    exact_mod_cast hreal
  simpa [Nat.mul_comm] using hnat

structure Z180K30GramJointEigenvalueData where
  eigenvalue : Fin 6 → Fin 5 → ℝ
  nonnegative : ∀ k r, 0 ≤ eigenvalue k r
  sum_eq_thirty : ∀ k, (∑ r, eigenvalue k r) = 30
  common_cross_product : ∀ k, ∃ q : ℝ,
    ∀ r s, r ≠ s → eigenvalue k r * eigenvalue k s = q
  trace_eq_thirtySix : ∀ r, (∑ k, eigenvalue k r) = 36

structure Z180K30ExceptionalGramEigenvalueData
    (lambda : Fin 6 → Fin 5 → ℝ) : Prop where
  coordinatePattern : ∀ k,
    Z180K30GramNormalScalar (lambda k) ∨
      Z180K30GramSpikeScalar (lambda k)
  oneUniform : z180K30GramUniformMultiplicity lambda = 1
  oneSpikeEach : ∀ r, z180K30GramSpikeMultiplicity lambda r = 1

theorem Z180K30GramJointEigenvalueData.coordinatePattern
    (data : Z180K30GramJointEigenvalueData) (k : Fin 6) :
    Z180K30GramNormalScalar (data.eigenvalue k) ∨
      Z180K30GramSpikeScalar (data.eigenvalue k) :=
  z180K30_five_scalar_gram_dichotomy
    (data.eigenvalue k) (data.sum_eq_thirty k)
      (data.common_cross_product k)

theorem Z180K30GramJointEigenvalueData.multiplicityEquation
    (data : Z180K30GramJointEigenvalueData) :
    ∀ r,
      6 * z180K30GramUniformMultiplicity data.eigenvalue +
        30 * z180K30GramSpikeMultiplicity data.eigenvalue r = 36 :=
  z180K30_trace_eq_multiplicity_equation data.eigenvalue
    data.coordinatePattern data.trace_eq_thirtySix

theorem Z180K30GramJointEigenvalueData.dichotomy
    (data : Z180K30GramJointEigenvalueData) :
    (∀ k, Z180K30GramNormalScalar (data.eigenvalue k)) ∨
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

#print axioms z180K30_trace_eq_multiplicity_equation
#print axioms Z180K30GramJointEigenvalueData.dichotomy

end Fuglede
