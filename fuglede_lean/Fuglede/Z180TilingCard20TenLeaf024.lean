import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_024
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ30 : z180ExactOrderTransform B 30 = 0)
    (hBZ45 : z180ExactOrderTransform B 45 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC15 := h.BC15
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC4 hBC5
  try simp only [z180ExactOrderTransform] at hBC10 hBC15 hBC20 hBC30 hBC60
  try simp only [z180ExactOrderTransform] at hB3z hB10z hBZ30 hBZ45
  omega

end Fuglede
