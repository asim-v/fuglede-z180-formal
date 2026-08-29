import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_018
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0)
    (hBZ20 : z180ExactOrderTransform B 20 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC9 := h.BC9
  have hBC12 := h.BC12
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC45 := h.BC45
  have hBC60 := h.BC60
  have hBC90 := h.BC90
  have hBC180 := h.BC180
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC9 hBC12 hBC20 hBC30 hBC45
  try simp only [z180ExactOrderTransform] at hBC60 hBC90 hBC180 hB3z hB10z
  try simp only [z180ExactOrderTransform] at hBZ18 hBZ36 hBZ90 hBZ20
  linarith

end Fuglede

