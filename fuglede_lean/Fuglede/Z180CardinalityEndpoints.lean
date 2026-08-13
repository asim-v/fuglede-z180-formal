import Fuglede.CardinalityEndpoints

/-!
# Cardinality endpoints at modulus 180

The general complement-space argument says that a proper spectral subset of
`ZMod 180` has cardinality at most `90`.  Thus every larger spectral set is the
whole group and tiles with the singleton zero.  This removes the entire upper
half of the cardinality case split without any arithmetic certificate.
-/

namespace Fuglede

/-- A spectral subset of `ZMod 180` either has size at most 90 or is the whole
group. -/
theorem z180_spectral_card_le_ninety_or_eq_univ
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    A.card <= 90 ∨ A = Finset.univ := by
  by_cases hproper : A = Finset.univ
  · exact Or.inr hproper
  · left
    have hFourier : FourierSpectrum A L :=
      (cyclotomicSpectrum_iff_fourierSpectrum A L).1 hSpec
    have hhalf := proper_fourierSpectrum_card_le_half hFourier hproper
    norm_num [ZMod.card] at hhalf
    omega

/-- Every spectral set in the strict upper half of `ZMod 180` is the whole
group. -/
theorem z180_spectral_eq_univ_of_ninety_lt_card
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hlarge : 90 < A.card) :
    A = Finset.univ := by
  rcases z180_spectral_card_le_ninety_or_eq_univ hSpec with hsmall | hfull
  · omega
  · exact hfull

/-- Consequently every spectral set in the strict upper half tiles, with the
explicit singleton complement. -/
theorem z180_exists_tiling_of_spectral_of_ninety_lt_card
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hlarge : 90 < A.card) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hfull := z180_spectral_eq_univ_of_ninety_lt_card hSpec hlarge
  subst A
  exact ⟨{0}, tiles_univ_singleton_zero⟩

#print axioms z180_spectral_card_le_ninety_or_eq_univ
#print axioms z180_exists_tiling_of_spectral_of_ninety_lt_card

end Fuglede
