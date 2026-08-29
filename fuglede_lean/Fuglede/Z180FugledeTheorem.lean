import Fuglede.Z180TilingSpectralClosureV12
import Fuglede.Z180K30UnconditionalCatalogueClosureV96

/-!
# Fuglede's conjecture for `ZMod 180`

For every subset of the cyclic group of order 180, translational tiling is
equivalent to spectrality.
-/

namespace Fuglede

/-- A finite subset of `ZMod 180` tiles if and only if it is spectral. -/
theorem z180_tiles_iff_spectral (A : Finset (ZMod 180)) :
    (∃ B : Finset (ZMod 180), Tiles A B) ↔
      ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  constructor
  · rintro ⟨B, hTiles⟩
    exact z180_exists_spectrum_of_tile_v12 hTiles
  · rintro ⟨L, hSpectrum⟩
    exact z180_exists_tiling_of_spectral_v96 hSpectrum

#print axioms z180_tiles_iff_spectral

end Fuglede
