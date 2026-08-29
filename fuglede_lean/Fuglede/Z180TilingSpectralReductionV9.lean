import Fuglede.Z180TilingCard12Descent
import Fuglede.Z180TilingSpectralReductionV8

/-! # Tiling-to-spectral reduction after the cardinality-12 case -/

namespace Fuglede

/-- Any remaining counterexample to tiling-implies-spectrality in `ZMod 180`
has cardinality `6`, `10`, or `30`. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v9
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 30 := by
  rcases z180_tiling_to_spectral_cardinality_reduction_v8 hTiles with
    hSpec | h6 | h10 | h12 | h30
  · exact Or.inl hSpec
  · right; omega
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_twelve hTiles h12)
  · right; omega

#print axioms z180_tiling_to_spectral_cardinality_reduction_v9

end Fuglede
