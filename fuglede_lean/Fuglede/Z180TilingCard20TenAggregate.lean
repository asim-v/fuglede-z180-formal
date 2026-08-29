import Fuglede.Z180TilingCard20TenLeaves00
import Fuglede.Z180TilingCard20TenLeaves01
import Fuglede.Z180TilingCard20TenLeaves02
import Fuglede.Z180TilingCard20TenLeaves03
import Fuglede.Z180TilingCard20TenLeaf016
import Fuglede.Z180TilingCard20TenLeaf017
import Fuglede.Z180TilingCard20TenLeaf018
import Fuglede.Z180TilingCard20TenLeaf019
import Fuglede.Z180TilingCard20TenLeaf020
import Fuglede.Z180TilingCard20TenLeaf021
import Fuglede.Z180TilingCard20TenLeaf022
import Fuglede.Z180TilingCard20TenLeaf023
import Fuglede.Z180TilingCard20TenLeaf024
import Fuglede.Z180TilingCard20TenLeaf025
import Fuglede.Z180TilingCard20TenLeaf026
import Fuglede.Z180TilingCard20TenLeaf027
import Fuglede.Z180TilingCard20TenLeaf028
import Fuglede.Z180TilingCard20TenLeaf029
import Fuglede.Z180TilingCard20TenLeaf030
import Fuglede.Z180TilingCard20TenLeaf031
import Fuglede.Z180TilingCard20TenLeaf032
import Fuglede.Z180TilingCard20TenLeaf033
import Fuglede.Z180TilingCard20TenLeaf034
import Fuglede.Z180TilingCard20TenLeaf035
import Fuglede.Z180TilingCard20TenLeaf036
import Fuglede.Z180TilingCard20TenLeaf037
import Fuglede.Z180TilingCard20TenLeaf038
import Fuglede.Z180TilingCard20TenLeaf039
import Fuglede.Z180TilingCard20TenLeaf040
import Fuglede.Z180TilingCard20TenLeaf041
import Fuglede.Z180TilingCard20TenLeaf042
import Fuglede.Z180TilingCard20TenLeaf043
import Fuglede.Z180TilingCard20TenLeaf044
import Fuglede.Z180TilingCard20TenLeaf045
import Fuglede.Z180TilingCard20TenLeaf046
import Fuglede.Z180TilingCard20TenLeaf047

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_transform_ten_zero_of_sharded_arithmetic
    {A B : Finset (ZMod 180)}
    (hAcard : A.card = 20) (hBcard : B.card = 9)
    (hA2 : z180ExactOrderTransform A 2 = 0)
    (hA4 : z180ExactOrderTransform A 4 = 0)
    (hA5 : z180ExactOrderTransform A 5 = 0)
    (hB3 : z180ExactOrderTransform B 3 = 0)
    (hB9 : z180ExactOrderTransform B 9 = 0)
    (hcover6 : z180ExactOrderTransform A 6 = 0 ∨
      z180ExactOrderTransform B 6 = 0)
    (hcover10 : z180ExactOrderTransform A 10 = 0 ∨
      z180ExactOrderTransform B 10 = 0)
    (hcover12 : z180ExactOrderTransform A 12 = 0 ∨
      z180ExactOrderTransform B 12 = 0)
    (hcover15 : z180ExactOrderTransform A 15 = 0 ∨
      z180ExactOrderTransform B 15 = 0)
    (hcover18 : z180ExactOrderTransform A 18 = 0 ∨
      z180ExactOrderTransform B 18 = 0)
    (hcover20 : z180ExactOrderTransform A 20 = 0 ∨
      z180ExactOrderTransform B 20 = 0)
    (hcover30 : z180ExactOrderTransform A 30 = 0 ∨
      z180ExactOrderTransform B 30 = 0)
    (hcover36 : z180ExactOrderTransform A 36 = 0 ∨
      z180ExactOrderTransform B 36 = 0)
    (hcover45 : z180ExactOrderTransform A 45 = 0 ∨
      z180ExactOrderTransform B 45 = 0)
    (hcover60 : z180ExactOrderTransform A 60 = 0 ∨
      z180ExactOrderTransform B 60 = 0)
    (hcover90 : z180ExactOrderTransform A 90 = 0 ∨
      z180ExactOrderTransform B 90 = 0)
    (hcover180 : z180ExactOrderTransform A 180 = 0 ∨
      z180ExactOrderTransform B 180 = 0) :
    z180ExactOrderTransform A 10 = 0 := by
  by_contra hA10ne
  have h := z180_card20_prepare_ten hAcard hBcard hA2 hA4 hA5 hB3 hB9
    hcover10 hA10ne
  by_cases hBZ6 : z180ExactOrderTransform B 6 = 0
  · by_cases hBZ18 : z180ExactOrderTransform B 18 = 0
    · exact z180_card20_ten_leaf_000 h hBZ6 hBZ18
    · have hAZ18 := hcover18.resolve_right hBZ18
      by_cases hBZ36 : z180ExactOrderTransform B 36 = 0
      · exact z180_card20_ten_leaf_001 h hBZ18 hBZ36
      · have hAZ36 := hcover36.resolve_right hBZ36
        by_cases hBZ180 : z180ExactOrderTransform B 180 = 0
        · exact z180_card20_ten_leaf_003 h hBZ6 hBZ36 hBZ180
        · have hAZ180 := hcover180.resolve_right hBZ180
          by_cases hBZ30 : z180ExactOrderTransform B 30 = 0
          · by_cases hBZ90 : z180ExactOrderTransform B 90 = 0
            · exact z180_card20_ten_leaf_011 h hBZ30 hBZ90
            · have hAZ90 := hcover90.resolve_right hBZ90
              by_cases hBZ20 : z180ExactOrderTransform B 20 = 0
              · by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · exact z180_card20_ten_leaf_020 h hBZ30 hBZ45
                · have hAZ45 := hcover45.resolve_right hBZ45
                  by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · exact z180_card20_ten_leaf_025 h hBZ30 hBZ20 hBZ60
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    exact z180_card20_ten_leaf_026 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ45 hAZ60
              · have hAZ20 := hcover20.resolve_right hBZ20
                exact z180_card20_ten_leaf_016 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ20
          · have hAZ30 := hcover30.resolve_right hBZ30
            by_cases hBZ90 : z180ExactOrderTransform B 90 = 0
            · exact z180_card20_ten_leaf_012 h hBZ6 hBZ90
            · have hAZ90 := hcover90.resolve_right hBZ90
              by_cases hBZ20 : z180ExactOrderTransform B 20 = 0
              · by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · exact z180_card20_ten_leaf_027 h hBZ6 hBZ20 hBZ45 hBZ60
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · by_cases hBZ15 : z180ExactOrderTransform B 15 = 0
                      · exact z180_card20_ten_leaf_042 h hBZ6 hBZ20 hBZ45 hBZ12 hBZ15
                      · have hAZ15 := hcover15.resolve_right hBZ15
                        exact z180_card20_ten_leaf_043 h hAZ18 hAZ36 hAZ180 hAZ30 hAZ90 hAZ60 hAZ15
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      exact z180_card20_ten_leaf_033 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ60 hAZ12
                · have hAZ45 := hcover45.resolve_right hBZ45
                  by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · by_cases hBZ15 : z180ExactOrderTransform B 15 = 0
                      · exact z180_card20_ten_leaf_044 h hBZ6 hBZ20 hBZ60 hBZ15
                      · have hAZ15 := hcover15.resolve_right hBZ15
                        exact z180_card20_ten_leaf_045 h hAZ18 hAZ36 hAZ180 hAZ30 hAZ90 hAZ15
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      by_cases hBZ15 : z180ExactOrderTransform B 15 = 0
                      · exact z180_card20_ten_leaf_046 h hBZ6 hBZ20 hBZ60 hBZ15
                      · have hAZ15 := hcover15.resolve_right hBZ15
                        exact z180_card20_ten_leaf_047 h hAZ18 hAZ36 hAZ180 hAZ30 hAZ90 hAZ15
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    exact z180_card20_ten_leaf_028 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ45 hAZ60
              · have hAZ20 := hcover20.resolve_right hBZ20
                exact z180_card20_ten_leaf_017 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ20
  · have hAZ6 := hcover6.resolve_right hBZ6
    by_cases hBZ18 : z180ExactOrderTransform B 18 = 0
    · by_cases hBZ36 : z180ExactOrderTransform B 36 = 0
      · by_cases hBZ180 : z180ExactOrderTransform B 180 = 0
        · by_cases hBZ30 : z180ExactOrderTransform B 30 = 0
          · exact z180_card20_ten_leaf_006 h hBZ18 hBZ36 hBZ30
          · have hAZ30 := hcover30.resolve_right hBZ30
            by_cases hBZ90 : z180ExactOrderTransform B 90 = 0
            · by_cases hBZ20 : z180ExactOrderTransform B 20 = 0
              · exact z180_card20_ten_leaf_018 h hBZ18 hBZ36 hBZ90 hBZ20
              · have hAZ20 := hcover20.resolve_right hBZ20
                by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · exact z180_card20_ten_leaf_029 h hBZ18 hBZ36 hBZ180 hBZ90 hBZ45 hBZ60
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · exact z180_card20_ten_leaf_034 h hBZ180 hBZ90 hBZ45 hBZ12
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      exact z180_card20_ten_leaf_035 h hAZ6 hAZ30 hAZ20 hAZ60 hAZ12
                · have hAZ45 := hcover45.resolve_right hBZ45
                  exact z180_card20_ten_leaf_021 h hBZ36 hBZ180 hBZ90 hBZ45
            · have hAZ90 := hcover90.resolve_right hBZ90
              exact z180_card20_ten_leaf_013 h hBZ18 hBZ36 hBZ180 hBZ90
        · have hAZ180 := hcover180.resolve_right hBZ180
          by_cases hBZ30 : z180ExactOrderTransform B 30 = 0
          · exact z180_card20_ten_leaf_007 h hBZ18 hBZ36 hBZ30
          · have hAZ30 := hcover30.resolve_right hBZ30
            by_cases hBZ90 : z180ExactOrderTransform B 90 = 0
            · exact z180_card20_ten_leaf_014 h hBZ18 hBZ36 hBZ180 hBZ90
            · have hAZ90 := hcover90.resolve_right hBZ90
              by_cases hBZ20 : z180ExactOrderTransform B 20 = 0
              · by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · exact z180_card20_ten_leaf_022 h hBZ18 hBZ36 hBZ20 hBZ45
                · have hAZ45 := hcover45.resolve_right hBZ45
                  by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · exact z180_card20_ten_leaf_030 h hBZ18 hBZ36 hBZ20 hBZ60
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · exact z180_card20_ten_leaf_036 h hBZ6 hBZ18 hBZ36 hBZ12
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      exact z180_card20_ten_leaf_037 h hAZ6 hAZ180 hAZ30 hAZ90 hAZ45 hAZ60 hAZ12
              · have hAZ20 := hcover20.resolve_right hBZ20
                by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · exact z180_card20_ten_leaf_023 h hBZ18 hBZ36 hBZ180 hBZ45
                · have hAZ45 := hcover45.resolve_right hBZ45
                  by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · exact z180_card20_ten_leaf_038 h hBZ18 hBZ36 hBZ60 hBZ12
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      exact z180_card20_ten_leaf_039 h hAZ6 hAZ180 hAZ30 hAZ90 hAZ20 hAZ45 hAZ12
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    by_cases hBZ12 : z180ExactOrderTransform B 12 = 0
                    · exact z180_card20_ten_leaf_040 h hBZ6 hBZ18 hBZ36 hBZ12
                    · have hAZ12 := hcover12.resolve_right hBZ12
                      exact z180_card20_ten_leaf_041 h hAZ6 hAZ180 hAZ30 hAZ90 hAZ20 hAZ45 hAZ12
      · have hAZ36 := hcover36.resolve_right hBZ36
        by_cases hBZ180 : z180ExactOrderTransform B 180 = 0
        · exact z180_card20_ten_leaf_004 h hBZ18 hBZ36 hBZ180
        · have hAZ180 := hcover180.resolve_right hBZ180
          by_cases hBZ30 : z180ExactOrderTransform B 30 = 0
          · exact z180_card20_ten_leaf_008 h hBZ18 hBZ30
          · have hAZ30 := hcover30.resolve_right hBZ30
            exact z180_card20_ten_leaf_009 h hAZ6 hAZ36 hAZ180 hAZ30
    · have hAZ18 := hcover18.resolve_right hBZ18
      by_cases hBZ36 : z180ExactOrderTransform B 36 = 0
      · exact z180_card20_ten_leaf_002 h hBZ18 hBZ36
      · have hAZ36 := hcover36.resolve_right hBZ36
        by_cases hBZ180 : z180ExactOrderTransform B 180 = 0
        · exact z180_card20_ten_leaf_005 h hBZ36 hBZ180
        · have hAZ180 := hcover180.resolve_right hBZ180
          by_cases hBZ30 : z180ExactOrderTransform B 30 = 0
          · by_cases hBZ90 : z180ExactOrderTransform B 90 = 0
            · exact z180_card20_ten_leaf_015 h hBZ30 hBZ90
            · have hAZ90 := hcover90.resolve_right hBZ90
              by_cases hBZ20 : z180ExactOrderTransform B 20 = 0
              · by_cases hBZ45 : z180ExactOrderTransform B 45 = 0
                · exact z180_card20_ten_leaf_024 h hBZ30 hBZ45
                · have hAZ45 := hcover45.resolve_right hBZ45
                  by_cases hBZ60 : z180ExactOrderTransform B 60 = 0
                  · exact z180_card20_ten_leaf_031 h hBZ30 hBZ20 hBZ60
                  · have hAZ60 := hcover60.resolve_right hBZ60
                    exact z180_card20_ten_leaf_032 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ45 hAZ60
              · have hAZ20 := hcover20.resolve_right hBZ20
                exact z180_card20_ten_leaf_019 h hAZ18 hAZ36 hAZ180 hAZ90 hAZ20
          · have hAZ30 := hcover30.resolve_right hBZ30
            exact z180_card20_ten_leaf_010 h hAZ6 hAZ36 hAZ180 hAZ30

#print axioms z180_card20_transform_ten_zero_of_sharded_arithmetic

end Fuglede




