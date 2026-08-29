import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_008
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ30 : z180ExactOrderTransform B 30 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC3 := h.BC3
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC10 := h.BC10
  have hBC20 := h.BC20
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC3 hBC5
  try simp only [z180ExactOrderTransform] at hBC6 hBC10 hBC20 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hB9z hB10z hBZ18 hBZ30
  omega

theorem z180_card20_ten_leaf_009
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ6 : z180ExactOrderTransform A 6 = 0)
    (hAZ36 : z180ExactOrderTransform A 36 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC3 := h.AC3
  have hAC6 := h.AC6
  have hAC36 := h.AC36
  have hAT2 := h.AT2
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC3 hAC6 hAC36
  try simp only [z180ExactOrderTransform] at hAT2 hA5z hA10p hAZ6 hAZ36
  try simp only [z180ExactOrderTransform] at hAZ180 hAZ30
  omega

theorem z180_card20_ten_leaf_010
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hAZ6 : z180ExactOrderTransform A 6 = 0)
    (hAZ36 : z180ExactOrderTransform A 36 = 0)
    (hAZ180 : z180ExactOrderTransform A 180 = 0)
    (hAZ30 : z180ExactOrderTransform A 30 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC3 := h.AC3
  have hAC6 := h.AC6
  have hAC36 := h.AC36
  have hAT2 := h.AT2
  have hA5z := h.A5z
  have hA10p := h.A10p
  try simp only [z180ExactOrderTransform] at hAsum hAone hAC3 hAC6 hAC36
  try simp only [z180ExactOrderTransform] at hAT2 hA5z hA10p hAZ6 hAZ36
  try simp only [z180ExactOrderTransform] at hAZ180 hAZ30
  omega

theorem z180_card20_ten_leaf_011
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ30 : z180ExactOrderTransform B 30 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC20 := h.BC20
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC5 hBC10
  try simp only [z180ExactOrderTransform] at hBC20 hB3z hB9z hB10z hBZ30
  try simp only [z180ExactOrderTransform] at hBZ90
  omega

end Fuglede


