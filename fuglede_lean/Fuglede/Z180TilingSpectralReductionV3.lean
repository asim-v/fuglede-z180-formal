import Fuglede.Z180TilingSpectralReductionV2
import Fuglede.Z180TilingCard36Closure

/-!
# Tiling-to-spectral reduction after closing cardinality 36

The explicit Ramanujan-energy argument for a `36 × 5` tiling removes
cardinality 36 from the list of possible counterexamples.
-/

namespace Fuglede

/-- Tiles of sizes `1`, `2`, `3`, `36`, `60`, `90`, and `180` are spectral.
Any remaining counterexample in `ZMod 180` has one of these eleven sizes. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v3
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 4 ∨ A.card = 5 ∨ A.card = 6 ∨ A.card = 9 ∨
      A.card = 10 ∨ A.card = 12 ∨ A.card = 15 ∨ A.card = 18 ∨
      A.card = 20 ∨ A.card = 30 ∨ A.card = 45 := by
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
  · exact Or.inl (z180_exists_spectrum_of_tile_card_thirty_six hTiles h)
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_sixty hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_ninety hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inr h))

#print axioms z180_tiling_to_spectral_cardinality_reduction_v3

end Fuglede
