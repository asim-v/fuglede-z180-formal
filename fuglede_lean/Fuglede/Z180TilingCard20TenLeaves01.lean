import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_004
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBNE36 : z180ExactOrderTransform B 36 ≠ 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hBP36 := lt_of_le_of_ne h.BT36 (Ne.symm hBNE36)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC10 hBC12 hBC15 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hBZ18 hBP36 hBZ180
  omega

theorem z180_card20_ten_leaf_005
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBNE36 : z180ExactOrderTransform B 36 ≠ 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC6 := h.BC6
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC20 := h.BC20
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hBP36 := lt_of_le_of_ne h.BT36 (Ne.symm hBNE36)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC4 hBC6 hBC10
  try simp only [z180ExactOrderTransform] at hBC12 hBC15 hBC20 hBC60 hB3z
  try simp only [z180ExactOrderTransform] at hB9z hBP36 hBZ180
  omega

theorem z180_card20_ten_leaf_006
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ30 : z180ExactOrderTransform B 30 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC3 := h.BC3
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC12 := h.BC12
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC3 hBC5
  try simp only [z180ExactOrderTransform] at hBC6 hBC12 hBC20 hBC30 hBC60
  try simp only [z180ExactOrderTransform] at hB3z hB10z hBZ18 hBZ36 hBZ30
  omega

theorem z180_card20_ten_leaf_007
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ18 : z180ExactOrderTransform B 18 = 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0)
    (hBZ30 : z180ExactOrderTransform B 30 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC3 := h.BC3
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC12 := h.BC12
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC3 hBC5
  try simp only [z180ExactOrderTransform] at hBC6 hBC12 hBC20 hBC30 hBC60
  try simp only [z180ExactOrderTransform] at hB3z hB10z hBZ18 hBZ36 hBZ30
  omega

end Fuglede


