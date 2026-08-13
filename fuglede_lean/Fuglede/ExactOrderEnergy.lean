import Fuglede.ExactOrderDistribution

/-!
# Fourier energy on an exact additive-order orbit

For a cyclic group, frequencies of the same additive order form one Galois
orbit.  The energy below is the sum of squared Fourier norms over that orbit.
It is manifestly nonnegative, and one cyclotomic zero of the given order
annihilates the entire energy.  These facts give the typed spectral
cross-implications used by the exact-order arithmetic relaxation.
-/

namespace Fuglede

open scoped BigOperators ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- Frequencies in `ZMod N` having additive order exactly `e`. -/
noncomputable def exactOrderFrequencies (e : ℕ) : Finset (ZMod N) :=
  Finset.univ.filter fun d ↦ frequencyOrder N d = e

@[simp]
theorem mem_exactOrderFrequencies {e : ℕ} {d : ZMod N} :
    d ∈ exactOrderFrequencies (N := N) e ↔ frequencyOrder N d = e := by
  simp [exactOrderFrequencies]

/-- Sum of squared Fourier norms over the exact-order frequency orbit. -/
noncomputable def exactOrderFourierEnergy
    (X : Finset (ZMod N)) (e : ℕ) : ℝ :=
  ∑ d ∈ exactOrderFrequencies (N := N) e,
    Complex.normSq (fourierSum X d)

theorem exactOrderFourierEnergy_nonneg
    (X : Finset (ZMod N)) (e : ℕ) :
    0 ≤ exactOrderFourierEnergy X e := by
  apply Finset.sum_nonneg
  intro d hd
  exact Complex.normSq_nonneg _

theorem exactOrderFourierEnergy_eq_zero_iff
    (X : Finset (ZMod N)) (e : ℕ) :
    exactOrderFourierEnergy X e = 0 ↔
      ∀ d : ZMod N, frequencyOrder N d = e → fourierSum X d = 0 := by
  constructor
  · intro hzero d hd
    have hall :
        ∀ u ∈ exactOrderFrequencies (N := N) e,
          Complex.normSq (fourierSum X u) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun u hu ↦ Complex.normSq_nonneg (fourierSum X u))).mp
      exact hzero
    exact Complex.normSq_eq_zero.mp
      (hall d (mem_exactOrderFrequencies.mpr hd))
  · intro hall
    apply Finset.sum_eq_zero
    intro d hd
    rw [Complex.normSq_eq_zero]
    exact hall d (mem_exactOrderFrequencies.mp hd)

theorem exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero
    (X : Finset (ZMod N)) (e : ℕ) :
    exactOrderFourierEnergy X e = 0 ↔
      ∀ d : ZMod N, frequencyOrder N d = e → CyclotomicZero N X d := by
  rw [exactOrderFourierEnergy_eq_zero_iff]
  simp only [cyclotomicZero_iff_fourierSum_zero]

/-- A single zero annihilates the whole exact-order Galois orbit. -/
theorem exactOrderFourierEnergy_eq_zero_of_cyclotomicZero
    {X : Finset (ZMod N)} {u : ZMod N} {e : ℕ}
    (horder : frequencyOrder N u = e)
    (hzero : CyclotomicZero N X u) :
    exactOrderFourierEnergy X e = 0 := by
  rw [exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero]
  intro d hd
  unfold CyclotomicZero at hzero ⊢
  rw [hd, ← horder]
  exact hzero

/-- Positive exact-order mass on `A` forces zero energy on its spectral dual. -/
theorem exactOrderFourierEnergy_L_eq_zero_of_distribution_A_pos
    {A L : Finset (ZMod N)}
    (hSpec : CyclotomicSpectrum N A L) {e : ℕ}
    (he : e ≠ 1)
    (hpos : 0 < exactOrderDistribution A e) :
    exactOrderFourierEnergy L e = 0 := by
  obtain ⟨x, hx, y, hy, horder⟩ :=
    exists_pair_of_exactOrderDistribution_pos hpos
  have hxy : x ≠ y := by
    intro hxy
    subst y
    simp only [sub_self] at horder
    have : frequencyOrder N (0 : ZMod N) = 1 :=
      (frequencyOrder_eq_one_iff (NeZero.ne N) 0).2 rfl
    apply he
    exact horder.symm.trans this
  have hdual := cyclotomicSpectrum_dual hSpec
  exact exactOrderFourierEnergy_eq_zero_of_cyclotomicZero horder
    (hdual.2.2 x hx y hy hxy)

/-- Symmetric cross implication. -/
theorem exactOrderFourierEnergy_A_eq_zero_of_distribution_L_pos
    {A L : Finset (ZMod N)}
    (hSpec : CyclotomicSpectrum N A L) {e : ℕ}
    (he : e ≠ 1)
    (hpos : 0 < exactOrderDistribution L e) :
    exactOrderFourierEnergy A e = 0 := by
  obtain ⟨x, hx, y, hy, horder⟩ :=
    exists_pair_of_exactOrderDistribution_pos hpos
  have hxy : x ≠ y := by
    intro hxy
    subst y
    simp only [sub_self] at horder
    have : frequencyOrder N (0 : ZMod N) = 1 :=
      (frequencyOrder_eq_one_iff (NeZero.ne N) 0).2 rfl
    apply he
    exact horder.symm.trans this
  exact exactOrderFourierEnergy_eq_zero_of_cyclotomicZero horder
    (hSpec.2.2 x hx y hy hxy)

end Fuglede
