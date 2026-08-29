import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_045
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ18 : z180ExactOrderTransform A 18 = 0)
    (hAZ36 : z180ExactOrderTransform A 36 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0)
    (hAZ90 : z180ExactOrderTransform A 90 = 0)
    (hAZ15 : z180ExactOrderTransform A 15 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC6 := h.AC6
  have hAC12 := h.AC12
  have hAC36 := h.AC36
  have hAC45 := h.AC45
  have hAC90 := h.AC90
  have hA2z := h.A2z
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC6 hAC12 hAC36
  try simp only [z180ExactOrderTransform] at hAC45 hAC90 hA2z hA5z hA10p
  try simp only [z180ExactOrderTransform] at hAZ18 hAZ36 hAZ180 hAZ30 hAZ90
  try simp only [z180ExactOrderTransform] at hAZ15
  linarith

end Fuglede

