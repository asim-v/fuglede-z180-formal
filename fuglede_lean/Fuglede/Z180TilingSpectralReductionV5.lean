import Fuglede.Z180TilingCard45Closure
import Fuglede.Z180TilingSpectralReductionV4

/-! # Tiling-to-spectral reduction after the cardinality-45 case -/

namespace Fuglede

/-- Any remaining counterexample to tiling-implies-spectrality in `ZMod 180`
has cardinality `6`, `10`, `12`, `15`, `18`, `20`, or `30`. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v5
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 12 ∨ A.card = 15 ∨
      A.card = 18 ∨ A.card = 20 ∨ A.card = 30 := by
  rcases z180_tile_card_cases hTiles with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inl h))
  · exact Or.inl (z180_exists_spectrum_of_tile_card_two hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_three hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_four hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_five hTiles h)
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_nine hTiles h)
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_thirty_six hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_forty_five hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_sixty hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_ninety hTiles h)
  · exact Or.inl (z180_exists_spectrum_of_tile_card_one_or_full hTiles (Or.inr h))

#print axioms z180_tiling_to_spectral_cardinality_reduction_v5

end Fuglede
