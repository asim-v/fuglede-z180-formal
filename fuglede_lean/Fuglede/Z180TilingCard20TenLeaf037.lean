import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_037
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ6 : z180ExactOrderTransform A 6 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0)
    (hAZ90 : z180ExactOrderTransform A 90 = 0)
    (hAZ45 : z180ExactOrderTransform A 45 = 0)
    (hAZ60 : z180ExactOrderTransform A 60 = 0)
    (hAZ12 : z180ExactOrderTransform A 12 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC15 := h.AC15
  have hAC36 := h.AC36
  have hAC45 := h.AC45
  have hAC90 := h.AC90
  have hA2z := h.A2z
  have hA4z := h.A4z
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC15 hAC36 hAC45
  try simp only [z180ExactOrderTransform] at hAC90 hA2z hA4z hA5z hA10p
  try simp only [z180ExactOrderTransform] at hAZ6 hAZ180 hAZ30 hAZ90 hAZ45
  try simp only [z180ExactOrderTransform] at hAZ60 hAZ12
  linarith

end Fuglede

