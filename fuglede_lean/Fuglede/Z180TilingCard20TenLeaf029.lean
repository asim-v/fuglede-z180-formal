import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_029
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0)
    (hBZ45 : z180ExactOrderTransform B 45 = 0)
    (hBZ60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC5 := h.BC5
  have hBC9 := h.BC9
  have hBC10 := h.BC10
  have hBC18 := h.BC18
  have hBC30 := h.BC30
  have hBC45 := h.BC45
  have hBC60 := h.BC60
  have hBC90 := h.BC90
  have hBC180 := h.BC180
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC5 hBC9 hBC10
  try simp only [z180ExactOrderTransform] at hBC18 hBC30 hBC45 hBC60 hBC90
  try simp only [z180ExactOrderTransform] at hBC180 hB10z hBZ18 hBZ36 hBZ180
  try simp only [z180ExactOrderTransform] at hBZ90 hBZ45 hBZ60
  linarith

end Fuglede

