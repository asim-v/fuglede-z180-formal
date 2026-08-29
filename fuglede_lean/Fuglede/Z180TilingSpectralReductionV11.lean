import Fuglede.Z36Card6TilingToSpectral
import Fuglede.Z180TilingSpectralReductionV10

/-! # Final tiling-to-spectral reduction before cardinality 30 -/

namespace Fuglede

/-- Any remaining counterexample to tiling-implies-spectrality in `ZMod 180`
has cardinality exactly `30`. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v11
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 30 := by
  rcases z180_tiling_to_spectral_cardinality_reduction_v10 hTiles with
    hSpec | h6 | h30
  · exact Or.inl hSpec
  · exact Or.inl (z180_exists_spectrum_of_tile_card_six hTiles h6)
  · exact Or.inr h30

#print axioms z180_tiling_to_spectral_cardinality_reduction_v11

end Fuglede
