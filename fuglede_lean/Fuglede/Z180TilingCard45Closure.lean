import Fuglede.Z180TilingCard45Conditional

/-! # Tiling implies spectrality at cardinality 45 in `ZMod 180` -/

namespace Fuglede

theorem z180_exists_spectrum_of_tile_card_forty_five
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 45) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨hT15, hT45⟩ := z180_tiling_card45_mixed_transform_zeros hTiles hcard
  have h15 := z180_cyclotomicZero_of_transform_zero
    (X := A) (e := 15) (d := (12 : ZMod 180)) (by norm_num) (by decide) hT15
  have h45 := z180_cyclotomicZero_of_transform_zero
    (X := A) (e := 45) (d := (4 : ZMod 180)) (by norm_num) (by decide) hT45
  exact z180_exists_spectrum_of_tile_card_forty_five_of_mixed_order_zeros
    hTiles hcard h15 h45

#print axioms z180_exists_spectrum_of_tile_card_forty_five

end Fuglede
