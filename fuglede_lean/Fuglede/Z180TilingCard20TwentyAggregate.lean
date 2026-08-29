import Fuglede.Z180TilingCard20TwentyLeaves

/-! # Sharded order-20 closure for a `20 × 9` tiling -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_transform_twenty_zero_of_sharded_arithmetic
    {A B : Finset (ZMod 180)}
    (hAcard : A.card = 20) (hBcard : B.card = 9)
    (hA2 : z180ExactOrderTransform A 2 = 0)
    (hA5 : z180ExactOrderTransform A 5 = 0)
    (hA10 : z180ExactOrderTransform A 10 = 0)
    (hB3 : z180ExactOrderTransform B 3 = 0)
    (hB9 : z180ExactOrderTransform B 9 = 0)
    (hcover12 : z180ExactOrderTransform A 12 = 0 ∨
      z180ExactOrderTransform B 12 = 0)
    (hcover20 : z180ExactOrderTransform A 20 = 0 ∨
      z180ExactOrderTransform B 20 = 0)
    (hcover36 : z180ExactOrderTransform A 36 = 0 ∨
      z180ExactOrderTransform B 36 = 0)
    (hcover60 : z180ExactOrderTransform A 60 = 0 ∨
      z180ExactOrderTransform B 60 = 0)
    (hcover180 : z180ExactOrderTransform A 180 = 0 ∨
      z180ExactOrderTransform B 180 = 0) :
    z180ExactOrderTransform A 20 = 0 := by
  by_contra hA20ne
  have h := z180_card20_prepare_twenty hAcard hBcard hA2 hA5 hA10
    hB3 hB9 hcover20 hA20ne
  by_cases hB180 : z180ExactOrderTransform B 180 = 0
  · by_cases hB60 : z180ExactOrderTransform B 60 = 0
    · exact z180_card20_twenty_leaf_B180_B60 h hB180 hB60
    · have hA60 := hcover60.resolve_right hB60
      by_cases hB12 : z180ExactOrderTransform B 12 = 0
      · exact z180_card20_twenty_leaf_B12_B180 h hB12 hB180
      · have hA12 := hcover12.resolve_right hB12
        exact z180_card20_twenty_leaf_A12_A60 h hA12 hA60
  · have hA180 := hcover180.resolve_right hB180
    by_cases hB36 : z180ExactOrderTransform B 36 = 0
    · by_cases hB60 : z180ExactOrderTransform B 60 = 0
      · exact z180_card20_twenty_leaf_B36_B60 h hB36 hB60
      · have hA60 := hcover60.resolve_right hB60
        by_cases hB12 : z180ExactOrderTransform B 12 = 0
        · exact z180_card20_twenty_leaf_B12_B36 h hB12 hB36
        · have hA12 := hcover12.resolve_right hB12
          exact z180_card20_twenty_leaf_A12_A60 h hA12 hA60
    · have hA36 := hcover36.resolve_right hB36
      exact z180_card20_twenty_leaf_A180_A36 h hA180 hA36

#print axioms z180_card20_transform_twenty_zero_of_sharded_arithmetic

end Fuglede
