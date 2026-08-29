import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_023
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBNE180 : z180ExactOrderTransform B 180 ≠ 0)
    (hBZ45 : z180ExactOrderTransform B 45 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hBP180 := lt_of_le_of_ne h.BT180 (Ne.symm hBNE180)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC4 hBC5
  try simp only [z180ExactOrderTransform] at hBC12 hBC15 hBC30 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hBZ18 hBZ36 hBP180 hBZ45
  linarith

end Fuglede

