import Fuglede.Z180TilingSpectralLargePrimeComplements

/-!
# Sharpened tiling-to-spectral reduction in `ZMod 180`

The prime-complement construction closes the divisor cases `60` and `90`.
Thus only twelve cardinalities remain after the elementary and large-tile
arguments.
-/

namespace Fuglede

/-- Tiles of sizes `1`, `2`, `3`, `60`, `90`, and `180` are spectral.  Any
remaining counterexample to tiling-implies-spectrality in `ZMod 180` has one
of the twelve displayed cardinalities. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v2
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 4 ∨ A.card = 5 ∨ A.card = 6 ∨ A.card = 9 ∨
      A.card = 10 ∨ A.card = 12 ∨ A.card = 15 ∨ A.card = 18 ∨
      A.card = 20 ∨ A.card = 30 ∨ A.card = 36 ∨ A.card = 45 := by
  rcases z180_tile_card_cases hTiles with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inl h))
  · exact Or.inl (z180_exists_spectrum_of_tile_card_two hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_three hTiles h)
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_sixty hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_ninety hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inr h))

#print axioms z180_tiling_to_spectral_cardinality_reduction_v2

end Fuglede
