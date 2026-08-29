import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_021
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0)
    (hBNE45 : z180ExactOrderTransform B 45 ≠ 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC6 := h.BC6
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hBT18 := h.BT18
  have hB3z := h.B3z
  have hBP45 := lt_of_le_of_ne h.BT45 (Ne.symm hBNE45)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC6 hBC12 hBC15
  try simp only [z180ExactOrderTransform] at hBC20 hBC30 hBC60 hBT18 hB3z
  try simp only [z180ExactOrderTransform] at hBZ36 hBZ180 hBZ90 hBP45
  linarith

end Fuglede

