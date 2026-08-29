import Fuglede.Z180TilingCard20TwentyCore

/-! # Six arithmetic leaves for the cardinality-20 order-20 proof -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_twenty_leaf_A12_A60
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hA12 : z180ExactOrderTransform A 12 = 0)
    (hA60 : z180ExactOrderTransform A 60 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC3 := h.AC3
  have hAC18 := h.AC18
  have hAT4 := h.AT4
  have hA2z := h.A2z
  have hA5z := h.A5z
  have hA10z := h.A10z
  have hA20p := h.A20p
  simp only [z180ExactOrderTransform] at hAT4 hA2z hA5z hA10z hA20p hA12 hA60
  linarith

theorem z180_card20_twenty_leaf_A180_A36
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hA180 : z180ExactOrderTransform A 180 = 0)
    (hA36 : z180ExactOrderTransform A 36 = 0) : False := by
  have hAsum := h.Asum
  have hAone := h.Aone
  have hAC6 := h.AC6
  have hAC9 := h.AC9
  have hAC18 := h.AC18
  have hAT4 := h.AT4
  have hA2z := h.A2z
  have hA5z := h.A5z
  have hA10z := h.A10z
  have hA20p := h.A20p
  simp only [z180ExactOrderTransform] at hAT4 hA2z hA5z hA10z hA20p hA180 hA36
  linarith

theorem z180_card20_twenty_leaf_B12_B180
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hB12 : z180ExactOrderTransform B 12 = 0)
    (hB180 : z180ExactOrderTransform B 180 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC6 := h.BC6
  have hBC9 := h.BC9
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC15 := h.BC15
  have hBC20 := h.BC20
  have hBC60 := h.BC60
  have hBC90 := h.BC90
  have hBT6 := h.BT6
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB20z := h.B20z
  simp only [z180ExactOrderTransform] at hBT6 hB3z hB9z hB20z hB12 hB180
  linarith

theorem z180_card20_twenty_leaf_B12_B36
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hB12 : z180ExactOrderTransform B 12 = 0)
    (hB36 : z180ExactOrderTransform B 36 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC20 := h.BC20
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB20z := h.B20z
  simp only [z180ExactOrderTransform] at hB3z hB9z hB20z hB12 hB36
  have hzero :
      9 * exactOrderDistributionInt B 2 +
        9 * exactOrderDistributionInt B 4 +
        9 * exactOrderDistributionInt B 5 +
        9 * exactOrderDistributionInt B 10 +
        9 * exactOrderDistributionInt B 20 = 0 := by
    linarith [hBsum, hBone, hB3z, hB9z]
  have hzeros :
      exactOrderDistributionInt B 2 = 0 ∧
        exactOrderDistributionInt B 4 = 0 ∧
        exactOrderDistributionInt B 5 = 0 ∧
        exactOrderDistributionInt B 10 = 0 ∧
        exactOrderDistributionInt B 20 = 0 := by
    clear hBsum hBone hB3z hB9z hB20z hB12 hB36
    omega
  rcases hzeros with ⟨h2, h4, h5, h10, h20⟩
  have hmod :
      -20 * exactOrderDistributionInt B 3 +
        20 * exactOrderDistributionInt B 6 -
        20 * exactOrderDistributionInt B 9 +
        20 * exactOrderDistributionInt B 18 = -144 := by
    linarith [hBsum, hBone, hB3z, hB9z, hB20z, hB12, hB36]
  clear hBsum hBone hB3z hB9z hB20z hB12 hB36
  omega

theorem z180_card20_twenty_leaf_B180_B60
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hB180 : z180ExactOrderTransform B 180 = 0)
    (hB60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC20 := h.BC20
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB20z := h.B20z
  simp only [z180ExactOrderTransform] at hB3z hB9z hB20z hB180 hB60
  linarith

theorem z180_card20_twenty_leaf_B36_B60
    {A B : Finset (ZMod 180)} (h : Z180Card20TwentyFacts A B)
    (hB36 : z180ExactOrderTransform B 36 = 0)
    (hB60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC3 := h.BC3
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC10 := h.BC10
  have hBC12 := h.BC12
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hB3z := h.B3z
  have hB9z := h.B9z
  have hB20z := h.B20z
  simp only [z180ExactOrderTransform] at hB3z hB9z hB20z hB36 hB60
  linarith

end Fuglede
