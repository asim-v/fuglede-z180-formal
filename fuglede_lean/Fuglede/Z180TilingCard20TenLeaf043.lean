import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_043
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ18 : z180ExactOrderTransform A 18 = 0)
    (hAZ36 : z180ExactOrderTransform A 36 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0)
    (hAZ90 : z180ExactOrderTransform A 90 = 0)
    (hAZ60 : z180ExactOrderTransform A 60 = 0)
    (hAZ15 : z180ExactOrderTransform A 15 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC6 := h.AC6
  have hAC12 := h.AC12
  have hAC18 := h.AC18
  have hAC36 := h.AC36
  have hAC45 := h.AC45
  have hAT2 := h.AT2
  have hA4z := h.A4z
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC6 hAC12 hAC18
  try simp only [z180ExactOrderTransform] at hAC36 hAC45 hAT2 hA4z hA5z
  try simp only [z180ExactOrderTransform] at hA10p hAZ18 hAZ36 hAZ180 hAZ30
  try simp only [z180ExactOrderTransform] at hAZ90 hAZ60 hAZ15
  linarith

end Fuglede

