import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_032
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ18 : z180ExactOrderTransform A 18 = 0)
    (hAZ36 : z180ExactOrderTransform A 36 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ90 : z180ExactOrderTransform A 90 = 0)
    (hAZ45 : z180ExactOrderTransform A 45 = 0)
    (hAZ60 : z180ExactOrderTransform A 60 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC9 := h.AC9
  have hAC12 := h.AC12
  have hAC18 := h.AC18
  have hAC30 := h.AC30
  have hAC36 := h.AC36
  have hAC45 := h.AC45
  have hA2z := h.A2z
  have hA4z := h.A4z
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC9 hAC12 hAC18
  try simp only [z180ExactOrderTransform] at hAC30 hAC36 hAC45 hA2z hA4z
  try simp only [z180ExactOrderTransform] at hA5z hA10p hAZ18 hAZ36 hAZ180
  try simp only [z180ExactOrderTransform] at hAZ90 hAZ45 hAZ60
  linarith

end Fuglede

