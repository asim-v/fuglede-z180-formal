import Fuglede.Z180TilingCard30Descent
import Fuglede.Z180TilingSpectralReductionV11

/-! # Unconditional tiling-to-spectral closure in `ZMod 180` -/

namespace Fuglede

/-- Every translational tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_v12
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  rcases z180_tiling_to_spectral_cardinality_reduction_v11 hTiles with
    hSpectrum | hcard30
  · exact hSpectrum
  · exact z180_exists_spectrum_of_tile_card_thirty hTiles hcard30

#print axioms z180_exists_spectrum_of_tile_v12

end Fuglede
