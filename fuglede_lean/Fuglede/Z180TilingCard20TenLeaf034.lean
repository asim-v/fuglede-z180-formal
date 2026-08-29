import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_034
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ180 : z180ExactOrderTransform B 180 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0)
    (hBZ45 : z180ExactOrderTransform B 45 = 0)
    (hBZ12 : z180ExactOrderTransform B 12 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC6 := h.BC6
  have hBC9 := h.BC9
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC18 := h.BC18
  have hBC20 := h.BC20
  have hBC60 := h.BC60
  have hBC90 := h.BC90
  have hBC180 := h.BC180
  have hBT18 := h.BT18
  have hBT36 := h.BT36
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC6 hBC9 hBC12
  try simp only [z180ExactOrderTransform] at hBC15 hBC18 hBC20 hBC60 hBC90
  try simp only [z180ExactOrderTransform] at hBC180 hBT18 hBT36 hB3z hB10z
  try simp only [z180ExactOrderTransform] at hBZ180 hBZ90 hBZ45 hBZ12
  linarith

end Fuglede

