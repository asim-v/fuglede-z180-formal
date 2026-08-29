import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_035
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ6 : z180ExactOrderTransform A 6 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0)
    (hAZ20 : z180ExactOrderTransform A 20 = 0)
    (hAZ60 : z180ExactOrderTransform A 60 = 0)
    (hAZ12 : z180ExactOrderTransform A 12 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC3 := h.AC3
  have hAC36 := h.AC36
  have hAT2 := h.AT2
  have hA4z := h.A4z
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC3 hAC36 hAT2
  try simp only [z180ExactOrderTransform] at hA4z hA5z hA10p hAZ6 hAZ30
  try simp only [z180ExactOrderTransform] at hAZ20 hAZ60 hAZ12
  linarith

end Fuglede

