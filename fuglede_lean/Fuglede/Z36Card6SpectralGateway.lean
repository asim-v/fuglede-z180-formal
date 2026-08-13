import Fuglede.Z36Card6DifferenceStructuralSharded
import Fuglede.Z36Card6TilingCovers
import Fuglede.Z180K6DescentImages

/-!
# Cardinality-six spectral gateway in `ZMod 36`

The exact difference classifier reduces the theorem to six small 0/1
cyclotomic implications.  This module records that forcing interface and
performs the complete spectrum-to-tiling dispatch.
-/

namespace Fuglede

/-- The compact set-side forcing facts left after the exact nine-pattern
difference classifier. -/
structure Z36Card6CyclotomicForcing : Prop where
  zero_3_9_impossible : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 3 → Z36ZeroAtOrder A 9 → False
  zero_3_18_forces_2_6 : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 3 → Z36ZeroAtOrder A 18 →
      Z36ZeroAtOrder A 2 ∧ Z36ZeroAtOrder A 6
  zero_3_36_forces_4_12 : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 3 → Z36ZeroAtOrder A 36 →
      Z36ZeroAtOrder A 4 ∧ Z36ZeroAtOrder A 12
  zero_36_forces_12_or_18 : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 36 →
      Z36ZeroAtOrder A 12 ∨ Z36ZeroAtOrder A 18
  zero_6_9_18_forces_2 : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 6 → Z36ZeroAtOrder A 9 → Z36ZeroAtOrder A 18 →
      Z36ZeroAtOrder A 2
  zero_9_12_36_forces_4 : ∀ A : Finset (ZMod 36), A.card = 6 →
    Z36ZeroAtOrder A 9 → Z36ZeroAtOrder A 12 → Z36ZeroAtOrder A 36 →
      Z36ZeroAtOrder A 4

/-- A witnessed exact difference order in a cyclotomic spectrum supplies the
corresponding set-side cyclotomic divisor. -/
theorem z36_zero_of_spectrum_difference
    {A L : Finset (ZMod 36)} (hSpec : CyclotomicSpectrum 36 A L)
    {m : Nat} (horder : Z36HasDifferenceOrder L m) :
    Z36ZeroAtOrder A m := by
  obtain ⟨x, hx, y, hy, hne, hm⟩ := horder
  have hz := hSpec.2.2 x hx y hy hne
  simpa [CyclotomicZero, Z36ZeroAtOrder, hm] using hz

/-- The six compact set-side forcing facts discharge the exact remaining
`ZMod 36`, cardinality-six induction premise. -/
theorem z36_spectral_card6_implies_tile_of_forcing
    (hforce : Z36Card6CyclotomicForcing) :
    Z36SpectralCard6ImpliesTile := by
  intro A L hcard hSpec
  have hcardL : L.card = 6 := by
    rw [← hSpec.2.1]
    exact hcard
  have hpats := z36_card6_nine_difference_patterns_structural_sharded L hcardL
  unfold Z36Card6NineDifferencePatterns at hpats
  rcases hpats with h | h | h | h | h | h | h | h | h
  · have h2 := z36_zero_of_spectrum_difference hSpec h.1
    have h3 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h6 := z36_zero_of_spectrum_difference hSpec h.2.2
    exact ⟨z36Card6Complement236,
      z36_card6_tiles_of_zeros_2_3_6 hcard h2 h3 h6⟩
  · have h2 := z36_zero_of_spectrum_difference hSpec h.1
    have h9 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h18 := z36_zero_of_spectrum_difference hSpec h.2.2
    exact ⟨z36Card6Complement2918,
      z36_card6_tiles_of_zeros_2_9_18 hcard h2 h9 h18⟩
  · have h3 := z36_zero_of_spectrum_difference hSpec h.1
    have h4 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h12 := z36_zero_of_spectrum_difference hSpec h.2.2
    exact ⟨z36Card6Complement3412,
      z36_card6_tiles_of_zeros_3_4_12 hcard h3 h4 h12⟩
  · have h3 := z36_zero_of_spectrum_difference hSpec h.1
    have h9 := z36_zero_of_spectrum_difference hSpec h.2
    exact (hforce.zero_3_9_impossible A hcard h3 h9).elim
  · have h3 := z36_zero_of_spectrum_difference hSpec h.1
    have h18 := z36_zero_of_spectrum_difference hSpec h.2
    obtain ⟨h2, h6⟩ := hforce.zero_3_18_forces_2_6 A hcard h3 h18
    exact ⟨z36Card6Complement236,
      z36_card6_tiles_of_zeros_2_3_6 hcard h2 h3 h6⟩
  · have h3 := z36_zero_of_spectrum_difference hSpec h.1
    have h36 := z36_zero_of_spectrum_difference hSpec h.2
    obtain ⟨h4, h12⟩ := hforce.zero_3_36_forces_4_12 A hcard h3 h36
    exact ⟨z36Card6Complement3412,
      z36_card6_tiles_of_zeros_3_4_12 hcard h3 h4 h12⟩
  · have h4 := z36_zero_of_spectrum_difference hSpec h.1
    have h9 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h36 := z36_zero_of_spectrum_difference hSpec h.2.2
    rcases hforce.zero_36_forces_12_or_18 A hcard h36 with h12 | h18
    · exact ⟨z36Card6Complement491236,
        z36_card6_tiles_of_zeros_4_9_12_36 hcard h4 h9 h12 h36⟩
    · exact ⟨z36Card6Complement491836,
        z36_card6_tiles_of_zeros_4_9_18_36 hcard h4 h9 h18 h36⟩
  · have h6 := z36_zero_of_spectrum_difference hSpec h.1
    have h9 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h18 := z36_zero_of_spectrum_difference hSpec h.2.2
    have h2 := hforce.zero_6_9_18_forces_2 A hcard h6 h9 h18
    exact ⟨z36Card6Complement2918,
      z36_card6_tiles_of_zeros_2_9_18 hcard h2 h9 h18⟩
  · have h9 := z36_zero_of_spectrum_difference hSpec h.1
    have h12 := z36_zero_of_spectrum_difference hSpec h.2.1
    have h36 := z36_zero_of_spectrum_difference hSpec h.2.2
    have h4 := hforce.zero_9_12_36_forces_4 A hcard h9 h12 h36
    exact ⟨z36Card6Complement491236,
      z36_card6_tiles_of_zeros_4_9_12_36 hcard h4 h9 h12 h36⟩

#print axioms z36_zero_of_spectrum_difference
#print axioms z36_spectral_card6_implies_tile_of_forcing

end Fuglede
