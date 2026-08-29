import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_031
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ30 : z180ExactOrderTransform B 30 = 0)
    (hBZ20 : z180ExactOrderTransform B 20 = 0)
    (hBZ60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC3 := h.BC3
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC15 := h.BC15
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC3 hBC5 hBC10
  try simp only [z180ExactOrderTransform] at hBC15 hBC20 hBC30 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hB10z hBZ30 hBZ20 hBZ60
  linarith

end Fuglede

