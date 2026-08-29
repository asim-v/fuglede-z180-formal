import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_036
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBNE6 : z180ExactOrderTransform B 6 ≠ 0)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ12 : z180ExactOrderTransform B 12 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC5 := h.BC5
  have hBC12 := h.BC12
  have hBC18 := h.BC18
  have hBC60 := h.BC60
  have hBC90 := h.BC90
  have hB3z := h.B3z
  have hBP6 := lt_of_le_of_ne h.BT6 (Ne.symm hBNE6)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC5 hBC12 hBC18
  try simp only [z180ExactOrderTransform] at hBC60 hBC90 hB3z hBP6 hBZ18
  try simp only [z180ExactOrderTransform] at hBZ36 hBZ12
  linarith

end Fuglede

