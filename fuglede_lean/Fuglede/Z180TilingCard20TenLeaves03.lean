import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_012
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ6 : z180ExactOrderTransform B 6 = 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC5 := h.BC5
  have hBC9 := h.BC9
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC18 := h.BC18
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC180 := h.BC180
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC5 hBC9
  try simp only [z180ExactOrderTransform] at hBC10 hBC12 hBC15 hBC18 hBC20
  try simp only [z180ExactOrderTransform] at hBC30 hBC180 hB3z hB9z hB10z
  try simp only [z180ExactOrderTransform] at hBZ6 hBZ90
  omega

theorem z180_card20_ten_leaf_013
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0)
    (hBNE90 : z180ExactOrderTransform B 90 ≠ 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hBP90 := lt_of_le_of_ne h.BT90 (Ne.symm hBNE90)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC4 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC10 hBC12 hBC30 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hBZ18 hBZ36 hBZ180 hBP90
  omega

theorem z180_card20_ten_leaf_014
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBNE180 : z180ExactOrderTransform B 180 ≠ 0)
    (hBZ90 : z180ExactOrderTransform B 90 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC12 := h.BC12
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hBP180 := lt_of_le_of_ne h.BT180 (Ne.symm hBNE180)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC12 hBC20 hBC30 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hBZ18 hBZ36 hBP180 hBZ90
  omega

theorem z180_card20_ten_leaf_015
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


