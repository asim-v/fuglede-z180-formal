import Fuglede.Z36Card6ForcingClosure
import Fuglede.Z36Card6TilingCover4936

/-!
# The common-spectrum compatibility endpoint needed by the `k = 30` fibres

This module deliberately does not claim that the five `ZMod 36` fibres of a
spectral set in `ZMod 180` have a common spectrum.  It records the exact
finite conclusion available once that compatibility premise is supplied:
five six-point sets sharing one six-point spectrum share one fixed tiling
complement.
-/

namespace Fuglede

/-- The explicit compatibility premise left for the `k = 30` fibre bridge. -/
def Z180K30FiveFibresHaveCommonZ36Spectrum
    (A : Fin 5 → Finset (ZMod 36)) (L : Finset (ZMod 36)) : Prop :=
  ∀ i, CyclotomicSpectrum 36 (A i) L

/-- The exact nine-pattern classifier and the sealed six-point forcing facts
choose one complement that tiles all five fibres simultaneously, provided
the fibres share the same spectrum. -/
theorem z180_k30_five_fibres_common_complement_of_common_spectrum
    (A : Fin 5 → Finset (ZMod 36)) (L : Finset (ZMod 36))
    (hcard : ∀ i, (A i).card = 6)
    (hcommon : Z180K30FiveFibresHaveCommonZ36Spectrum A L) :
    ∃ B : Finset (ZMod 36), ∀ i, Tiles (A i) B := by
  have hcardL : L.card = 6 := by
    rw [← (hcommon (0 : Fin 5)).2.1]
    exact hcard 0
  have hpats := z36_card6_nine_difference_patterns_structural_sharded L hcardL
  have hforce : Z36Card6CyclotomicForcing := z36_card6_cyclotomic_forcing
  unfold Z36Card6NineDifferencePatterns at hpats
  rcases hpats with h | h | h | h | h | h | h | h | h
  · refine ⟨z36Card6Complement236, ?_⟩
    intro i
    have h2 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h3 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h6 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    exact z36_card6_tiles_of_zeros_2_3_6 (hcard i) h2 h3 h6
  · refine ⟨z36Card6Complement2918, ?_⟩
    intro i
    have h2 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h9 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h18 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    exact z36_card6_tiles_of_zeros_2_9_18 (hcard i) h2 h9 h18
  · refine ⟨z36Card6Complement3412, ?_⟩
    intro i
    have h3 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h4 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h12 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    exact z36_card6_tiles_of_zeros_3_4_12 (hcard i) h3 h4 h12
  · have h3 := z36_zero_of_spectrum_difference (hcommon (0 : Fin 5)) h.1
    have h9 := z36_zero_of_spectrum_difference (hcommon (0 : Fin 5)) h.2
    exact (hforce.zero_3_9_impossible (A 0) (hcard 0) h3 h9).elim
  · refine ⟨z36Card6Complement236, ?_⟩
    intro i
    have h3 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h18 := z36_zero_of_spectrum_difference (hcommon i) h.2
    obtain ⟨h2, h6⟩ :=
      hforce.zero_3_18_forces_2_6 (A i) (hcard i) h3 h18
    exact z36_card6_tiles_of_zeros_2_3_6 (hcard i) h2 h3 h6
  · refine ⟨z36Card6Complement3412, ?_⟩
    intro i
    have h3 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h36 := z36_zero_of_spectrum_difference (hcommon i) h.2
    obtain ⟨h4, h12⟩ :=
      hforce.zero_3_36_forces_4_12 (A i) (hcard i) h3 h36
    exact z36_card6_tiles_of_zeros_3_4_12 (hcard i) h3 h4 h12
  · refine ⟨z36Card6Complement4936, ?_⟩
    intro i
    have h4 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h9 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h36 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    exact z36_card6_tiles_of_zeros_4_9_36 (hcard i) h4 h9 h36
  · refine ⟨z36Card6Complement2918, ?_⟩
    intro i
    have h6 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h9 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h18 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    have h2 := hforce.zero_6_9_18_forces_2 (A i) (hcard i) h6 h9 h18
    exact z36_card6_tiles_of_zeros_2_9_18 (hcard i) h2 h9 h18
  · refine ⟨z36Card6Complement491236, ?_⟩
    intro i
    have h9 := z36_zero_of_spectrum_difference (hcommon i) h.1
    have h12 := z36_zero_of_spectrum_difference (hcommon i) h.2.1
    have h36 := z36_zero_of_spectrum_difference (hcommon i) h.2.2
    have h4 := hforce.zero_9_12_36_forces_4 (A i) (hcard i) h9 h12 h36
    exact z36_card6_tiles_of_zeros_4_9_12_36 (hcard i) h4 h9 h12 h36

#print axioms z180_k30_five_fibres_common_complement_of_common_spectrum

end Fuglede
