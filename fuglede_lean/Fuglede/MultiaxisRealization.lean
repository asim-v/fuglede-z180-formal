import Fuglede.MultiAxisBounds
import Fuglede.LabaMarshallCyclotomic

/-!
# Realizing the arithmetic relaxation from spectrality

This file assembles all non-capacity fields of `MultiaxisConstraints` from a
genuine cyclotomic spectral pair.  The four explicit bound hypotheses are
kept visible until the companion support-valency/projection-bound module is
imported; the final corollary will discharge them uniformly for every set.
-/

namespace Fuglede

open scoped BigOperators

private theorem finTwo_eq_zero_or_one (side : Fin 2) :
    side = 0 ∨ side = 1 := by
  by_cases hzero : side = 0
  · exact Or.inl hzero
  · right
    apply Fin.ext
    have hval : side.val ≠ 0 := by
      intro h
      apply hzero
      apply Fin.ext
      simpa using h
    omega

/-- Spectrality supplies the complete multiaxis system once the two elementary
inner-distribution bounds and the two projection bounds are available. -/
theorem cyclotomicSpectrum_yields_multiaxisConstraints_of_bounds
    {A L : Finset (ZMod 2310)}
    (hSpec : CyclotomicSpectrum 2310 A L)
    (hsquare : ∀ side D, D ≠ ∅ →
      spectralPairDistribution A L side D ≤ (A.card ^ 2 : Nat))
    (hvalency : ∀ side D, D ≠ ∅ →
      spectralPairDistribution A L side D ≤
        (A.card * supportValency D : Nat))
    (hprojectionLower : ∀ side S,
      (balancedCollisionLower A.card (supportModulus S) : Int) ≤
        multiaxisProjectionCollision
          (spectralPairDistribution A L) side S)
    (hprojectionUpper : ∀ side S,
      multiaxisProjectionCollision
          (spectralPairDistribution A L) side S ≤
        (projectionCapacityUpper A.card (supportModulus S) : Int)) :
    MultiaxisConstraints A.card
      (spectralPairDistribution A L) (spectralPairEnergyZero A L) := by
  refine
    { diagonal := ?_
      nonnegative := ?_
      square_bound := hsquare
      valency_bound := hvalency
      even_off_diagonal := ?_
      total_mass := ?_
      projection_lower := hprojectionLower
      projection_upper := hprojectionUpper
      energy_nonnegative := ?_
      zero_iff_energy := ?_
      zero_empty_false := ?_
      prime_exclusion := ?_
      laba_marshall := ?_
      cross_set_to_spectrum := ?_
      cross_spectrum_to_set := ?_ }
  · intro side
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · simp [innerDistributionInt]
    · simp [innerDistributionInt, ← hSpec.2.1]
  · intro side D
    rcases finTwo_eq_zero_or_one side with rfl | rfl <;>
      simp [spectralPairDistribution, innerDistributionInt]
  · intro side D hD
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · change Even (innerDistributionInt A D)
      unfold innerDistributionInt
      exact_mod_cast innerDistribution_even_of_nonempty A hD
    · change Even (innerDistributionInt L D)
      unfold innerDistributionInt
      exact_mod_cast innerDistribution_even_of_nonempty L hD
  · intro side
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · change (∑ D : AxisSupport2310, innerDistributionInt A D) =
        (A.card ^ 2 : Nat)
      unfold innerDistributionInt
      exact_mod_cast sum_innerDistribution A
    · change (∑ D : AxisSupport2310, innerDistributionInt L D) =
        (A.card ^ 2 : Nat)
      unfold innerDistributionInt
      have hsum := sum_innerDistribution L
      rw [← hSpec.2.1] at hsum
      exact_mod_cast hsum
  · intro side D hD
    rcases finTwo_eq_zero_or_one side with rfl | rfl <;>
      simp [multiaxisEnergy_spectralPairDistribution_set,
        multiaxisEnergy_spectralPairDistribution_spectrum,
        supportEnergy_nonneg]
  · intro side D hD
    rcases finTwo_eq_zero_or_one side with rfl | rfl <;>
      simp [spectralPairEnergyZero,
        multiaxisEnergy_spectralPairDistribution_set,
        multiaxisEnergy_spectralPairDistribution_spectrum]
  · intro side
    have hApos : 0 < A.card := hSpec.1.card_pos
    have hLpos : 0 < L.card := by simpa [← hSpec.2.1] using hApos
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · intro hzero
      have henergy : supportEnergy A ∅ = 0 := by
        simpa [spectralPairEnergyZero] using hzero
      rw [supportEnergy_empty] at henergy
      have hcard : (0 : Int) < A.card := by exact_mod_cast hApos
      nlinarith
    · intro hzero
      have henergy : supportEnergy L ∅ = 0 := by
        simpa [spectralPairEnergyZero] using hzero
      rw [supportEnergy_empty] at henergy
      have hcard : (0 : Int) < L.card := by exact_mod_cast hLpos
      nlinarith
  · intro side i hnot
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · constructor
      · intro hzero
        apply supportEnergy_singleton_ne_zero_of_not_dvd A i hnot
        simpa [spectralPairEnergyZero] using hzero
      · change (innerDistribution A {i} : Int) = 0
        exact_mod_cast
          innerDistribution_A_singleton_eq_zero_of_not_dvd hSpec i hnot
    · have hnotL : ¬ crt2310Modulus i ∣ L.card := by
        simpa [← hSpec.2.1] using hnot
      constructor
      · intro hzero
        apply supportEnergy_singleton_ne_zero_of_not_dvd L i hnotL
        simpa [spectralPairEnergyZero] using hzero
      · change (innerDistribution L {i} : Int) = 0
        exact_mod_cast
          innerDistribution_L_singleton_eq_zero_of_not_dvd hSpec i hnot
  · intro side base added hdisjoint hlarge hparents
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · apply supportEnergy_base_eq_zero_of_labaMarshall
          A base added hdisjoint hlarge
      intro i hi
      simpa [spectralPairEnergyZero] using hparents i hi
    · have hlargeL : L.card < supportModulus added := by
        rw [← hSpec.2.1]
        exact hlarge
      apply supportEnergy_base_eq_zero_of_labaMarshall
          L base added hdisjoint hlargeL
      intro i hi
      simpa [spectralPairEnergyZero] using hparents i hi
  · intro D hD hpos
    change (0 : Int) < (innerDistribution A D : Int) at hpos
    change supportEnergy L D = 0
    apply supportEnergy_L_eq_zero_of_innerDistribution_A_pos hSpec hD
    exact_mod_cast hpos
  · intro D hD hpos
    change (0 : Int) < (innerDistribution L D : Int) at hpos
    change supportEnergy A D = 0
    apply supportEnergy_A_eq_zero_of_innerDistribution_L_pos hSpec hD
    exact_mod_cast hpos

/-- Every cyclotomic spectral pair in `ZMod 2310` realizes the complete
five-axis arithmetic relaxation used by the finite certificate campaign. -/
theorem cyclotomicSpectrum_yields_multiaxisConstraints
    {A L : Finset (ZMod 2310)}
    (hSpec : CyclotomicSpectrum 2310 A L) :
    MultiaxisConstraints A.card
      (spectralPairDistribution A L) (spectralPairEnergyZero A L) := by
  apply cyclotomicSpectrum_yields_multiaxisConstraints_of_bounds hSpec
  · intro side D _
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · change (innerDistribution A D : Int) ≤ (A.card ^ 2 : Nat)
      exact_mod_cast innerDistribution_le_card_sq A D
    · change (innerDistribution L D : Int) ≤ (A.card ^ 2 : Nat)
      have hbound := innerDistribution_le_card_sq L D
      rw [hSpec.2.1]
      exact_mod_cast hbound
  · intro side D _
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · change (innerDistribution A D : Int) ≤
          (A.card * supportValency D : Nat)
      exact_mod_cast innerDistribution_le_card_mul_supportValency A D
    · change (innerDistribution L D : Int) ≤
          (A.card * supportValency D : Nat)
      have hbound := innerDistribution_le_card_mul_supportValency L D
      rw [hSpec.2.1]
      exact_mod_cast hbound
  · intro side S
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · rw [multiaxisProjectionCollision_spectralPairDistribution_set]
      exact projectionPairCount_lower_relaxation A S
    · rw [multiaxisProjectionCollision_spectralPairDistribution_spectrum]
      have hbound := projectionPairCount_lower_relaxation L S
      simpa [hSpec.2.1] using hbound
  · intro side S
    rcases finTwo_eq_zero_or_one side with rfl | rfl
    · rw [multiaxisProjectionCollision_spectralPairDistribution_set]
      exact projectionPairCount_upper_relaxation A S
    · rw [multiaxisProjectionCollision_spectralPairDistribution_spectrum]
      have hbound := projectionPairCount_upper_relaxation L S
      simpa [hSpec.2.1] using hbound

end Fuglede
