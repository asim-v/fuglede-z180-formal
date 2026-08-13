import Fuglede.Z180CardinalityEndpoints
import Fuglede.Z180SmallCardinality

/-!
# Trivial cardinality endpoints in `ZMod 180`

This file records the two endpoint cases needed by the explicit divisor split.
A singleton tiles by translating the standard singleton-zero tiling, while a
spectral set of cardinality 180 lies in the strict upper half and is therefore
the whole group.
-/

namespace Fuglede

/-- Every singleton subset of `ZMod 180` tiles, independently of spectrality. -/
theorem z180_exists_tiling_of_card_one {A : Finset (ZMod 180)}
    (hcard : A.card = 1) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨Finset.univ, ?_⟩
  simpa using
    (tiles_translate_left (G := ZMod 180) a
      (tiles_singleton_zero_univ (G := ZMod 180)))

/-- A spectral subset of `ZMod 180` with full cardinality tiles. -/
theorem z180_exists_tiling_of_spectral_card_one_eighty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 180) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_exists_tiling_of_spectral_of_ninety_lt_card hSpec
  omega

#print axioms z180_exists_tiling_of_card_one
#print axioms z180_exists_tiling_of_spectral_card_one_eighty

end Fuglede
