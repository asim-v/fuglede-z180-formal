import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_000
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ6 : z180ExactOrderTransform B 6 = 0)
    (hBZ18 : z180ExactOrderTransform B 18 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC20 := h.BC20
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC4 hBC5
  try simp only [z180ExactOrderTransform] at hBC10 hBC20 hB3z hB9z hB10z
  try simp only [z180ExactOrderTransform] at hBZ6 hBZ18
  omega

theorem z180_card20_ten_leaf_001
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBNE18 : z180ExactOrderTransform B 18 ≠ 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hBP18 := lt_of_le_of_ne h.BT18 (Ne.symm hBNE18)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC4 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC20 hBC30 hB3z hB9z hBP18
  try simp only [z180ExactOrderTransform] at hBZ36
  omega

theorem z180_card20_ten_leaf_002
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBNE18 : z180ExactOrderTransform B 18 ≠ 0)
    (hBZ36 : z180ExactOrderTransform B 36 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hBP18 := lt_of_le_of_ne h.BT18 (Ne.symm hBNE18)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC4 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC20 hBC30 hB3z hB9z hBP18
  try simp only [z180ExactOrderTransform] at hBZ36
  omega

theorem z180_card20_ten_leaf_003
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ6 : z180ExactOrderTransform B 6 = 0)
    (hBNE36 : z180ExactOrderTransform B 36 ≠ 0)
    (hBZ180 : z180ExactOrderTransform B 180 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC9 := h.BC9
  have hBC10 := h.BC10
  have hBC15 := h.BC15
  have hBC18 := h.BC18
  have hBC20 := h.BC20
  have hBC60 := h.BC60
  have hBC180 := h.BC180
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB10z := h.B10z
  have hBP36 := lt_of_le_of_ne h.BT36 (Ne.symm hBNE36)
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC4 hBC5 hBC6
  try simp only [z180ExactOrderTransform] at hBC9 hBC10 hBC15 hBC18 hBC20
  try simp only [z180ExactOrderTransform] at hBC60 hBC180 hB3z hB9z hB10z
  try simp only [z180ExactOrderTransform] at hBZ6 hBP36 hBZ180
  omega

end Fuglede


