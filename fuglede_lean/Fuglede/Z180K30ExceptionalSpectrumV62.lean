import Fuglede.Z180K30DephasedGramDichotomyV54
import Mathlib.Tactic

/-!
# The fixed spectrum in the exceptional K30 Gram branch

The multiplicity statement in the scalar dichotomy says more concretely that,
for every row block, exactly one joint eigenvector has eigenvalue six, exactly
one has eigenvalue thirty, and the remaining four have eigenvalue zero.
-/

namespace Fuglede

noncomputable section

theorem Z180K30ExceptionalGramEigenvalueData.exists_row_normal_spike_zero_v62
    {lambda : Fin 6 → Fin 5 → ℝ}
    (hex : Z180K30ExceptionalGramEigenvalueData lambda) (r : Fin 5) :
    ∃ k6 k30 : Fin 6,
      k6 ≠ k30 ∧
      Z180K30GramNormalScalar (lambda k6) ∧
      Z180K30GramSpikeAt (lambda k30) r ∧
      ∀ k, k ≠ k6 → k ≠ k30 → lambda k r = 0 := by
  classical
  have hnormalCard :
      ((Finset.univ : Finset (Fin 6)).filter fun k =>
        Z180K30GramNormalScalar (lambda k)).card = 1 := by
    simpa [z180K30GramUniformMultiplicity] using hex.oneUniform
  obtain ⟨k6, hk6set⟩ := Finset.card_eq_one.mp hnormalCard
  have hk6normal : Z180K30GramNormalScalar (lambda k6) := by
    have hk6mem : k6 ∈
        (Finset.univ : Finset (Fin 6)).filter fun k =>
          Z180K30GramNormalScalar (lambda k) := by
      rw [hk6set]
      simp
    exact (Finset.mem_filter.mp hk6mem).2
  have hspikeCard :
      ((Finset.univ : Finset (Fin 6)).filter fun k =>
        Z180K30GramSpikeAt (lambda k) r).card = 1 := by
    simpa [z180K30GramSpikeMultiplicity] using hex.oneSpikeEach r
  obtain ⟨k30, hk30set⟩ := Finset.card_eq_one.mp hspikeCard
  have hk30spike : Z180K30GramSpikeAt (lambda k30) r := by
    have hk30mem : k30 ∈
        (Finset.univ : Finset (Fin 6)).filter fun k =>
          Z180K30GramSpikeAt (lambda k) r := by
      rw [hk30set]
      simp
    exact (Finset.mem_filter.mp hk30mem).2
  have hkne : k6 ≠ k30 := by
    intro h
    subst k30
    exact (hk6normal.not_spikeAt r) hk30spike
  refine ⟨k6, k30, hkne, hk6normal, hk30spike, ?_⟩
  intro k hk6 hk30
  rcases hex.coordinatePattern k with hnormal | ⟨owner, howner⟩
  · have hkmem : k ∈
        (Finset.univ : Finset (Fin 6)).filter fun j =>
          Z180K30GramNormalScalar (lambda j) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hnormal⟩
    rw [hk6set] at hkmem
    exact (hk6 (Finset.mem_singleton.mp hkmem)).elim
  · by_cases hor : owner = r
    · subst owner
      have hkmem : k ∈
          (Finset.univ : Finset (Fin 6)).filter fun j =>
            Z180K30GramSpikeAt (lambda j) r := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, howner⟩
      rw [hk30set] at hkmem
      exact (hk30 (Finset.mem_singleton.mp hkmem)).elim
    · exact howner.2 r (Ne.symm hor)

#print axioms
  Z180K30ExceptionalGramEigenvalueData.exists_row_normal_spike_zero_v62

end
end Fuglede
