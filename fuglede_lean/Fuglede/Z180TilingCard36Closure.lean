import Fuglede.Z180TilingCard36Order36

/-!
# The `36 × 5` tiling-to-spectral closure in `ZMod 180`

The four mixed exact-order transforms are forced to vanish by the specialized
Ramanujan-energy argument.  Together with the prime-power zeros, they give the
explicit lifted spectrum of cardinality 36.
-/

namespace Fuglede

/-- The mixed-order `T2` closure for a `36 × 5` tiling of `ZMod 180`. -/
theorem z180_tile_card_thirty_six_mixed_order_zeros
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36) :
    CyclotomicZero 180 A (30 : ZMod 180) ∧
    CyclotomicZero 180 A (15 : ZMod 180) ∧
    CyclotomicZero 180 A (10 : ZMod 180) ∧
    CyclotomicZero 180 A (5 : ZMod 180) := by
  have h6 := z180_tiling_card36_transform_six_zero hTiles hcard
  have h12 := z180_tiling_card36_transform_twelve_zero hTiles hcard h6
  have h18 := z180_tiling_card36_transform_eighteen_zero hTiles hcard h6 h12
  have h36 := z180_tiling_card36_transform_thirty_six_zero
    hTiles hcard h6 h12 h18
  exact ⟨
    z180_cyclotomicZero_of_transform_zero (by norm_num) (by decide) h6,
    z180_cyclotomicZero_of_transform_zero (by norm_num) (by decide) h12,
    z180_cyclotomicZero_of_transform_zero (by norm_num) (by decide) h18,
    z180_cyclotomicZero_of_transform_zero (by norm_num) (by decide) h36⟩

/-- Every 36-point translational tile in `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_thirty_six
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨h6, h12, h18, h36⟩ :=
    z180_tile_card_thirty_six_mixed_order_zeros hTiles hcard
  exact z180_exists_spectrum_of_tile_card_thirty_six_of_mixed_order_zeros
    hTiles hcard h6 h12 h18 h36

#print axioms z180_tile_card_thirty_six_mixed_order_zeros
#print axioms z180_exists_spectrum_of_tile_card_thirty_six

end Fuglede
