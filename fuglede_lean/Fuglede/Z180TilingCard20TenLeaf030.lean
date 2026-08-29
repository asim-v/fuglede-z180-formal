import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_030
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ20 : z180ExactOrderTransform B 20 = 0)
    (hBZ60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC3 := h.BC3
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC3 hBC5
  try simp only [z180ExactOrderTransform] at hBC10 hBC12 hBC30 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hBZ18 hBZ36 hBZ20 hBZ60
  linarith

end Fuglede

