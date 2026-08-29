import Fuglede.Z180TilingCard15Descent
import Fuglede.Z180TilingSpectralReductionV6

/-! # Tiling-to-spectral reduction after the cardinality-15 case -/

namespace Fuglede

/-- Any remaining counterexample to tiling-implies-spectrality in `ZMod 180`
has cardinality `6`, `10`, `12`, `18`, or `30`. -/
theorem z180_tiling_to_spectral_cardinality_reduction_v7
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    (∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 12 ∨
      A.card = 18 ∨ A.card = 30 := by
  rcases z180_tiling_to_spectral_cardinality_reduction_v6 hTiles with
    hSpec | h6 | h10 | h12 | h15 | h18 | h30
  · exact Or.inl hSpec
  · right; omega
  · right; omega
  · right; omega
  · exact Or.inl (z180_exists_spectrum_of_tile_card_fifteen hTiles h15)
  · right; omega
  · right; omega

#print axioms z180_tiling_to_spectral_cardinality_reduction_v7

end Fuglede
