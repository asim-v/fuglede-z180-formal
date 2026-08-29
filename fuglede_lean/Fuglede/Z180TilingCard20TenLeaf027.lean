import Fuglede.Z180TilingCard20TenCore

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card20_ten_leaf_027
    {A B : Finset (ZMod 180)} (h : Z180Card20TenFacts A B)
    (hBZ6 : z180ExactOrderTransform B 6 = 0)
    (hBZ20 : z180ExactOrderTransform B 20 = 0)
    (hBZ45 : z180ExactOrderTransform B 45 = 0)
    (hBZ60 : z180ExactOrderTransform B 60 = 0) : False := by
  have hBsum := h.Bsum
  have hBone := h.Bone
  have hBC2 := h.BC2
  have hBC3 := h.BC3
  have hBC4 := h.BC4
  have hBC5 := h.BC5
  have hBC9 := h.BC9
  have hBC10 := h.BC10
  have hBC15 := h.BC15
  have hBC18 := h.BC18
  have hBC20 := h.BC20
  have hBC30 := h.BC30
  have hBC60 := h.BC60
  have hBC180 := h.BC180
  have hB3z := h.B3z
  have hB10z := h.B10z
  try simp only [z180ExactOrderTransform] at hBsum hBone hBC2 hBC3 hBC4
  try simp only [z180ExactOrderTransform] at hBC5 hBC9 hBC10 hBC15 hBC18
  try simp only [z180ExactOrderTransform] at hBC20 hBC30 hBC60 hBC180 hB3z
  try simp only [z180ExactOrderTransform] at hB10z hBZ6 hBZ20 hBZ45 hBZ60
  have hzero :
      36 * exactOrderDistributionInt B 2 +
        36 * exactOrderDistributionInt B 4 +
        6 * exactOrderDistributionInt B 5 +
        6 * exactOrderDistributionInt B 10 +
        15 * exactOrderDistributionInt B 15 +
        6 * exactOrderDistributionInt B 20 +
        15 * exactOrderDistributionInt B 30 +
        15 * exactOrderDistributionInt B 60 = 0 := by
    linarith [hBsum, hBone, hB3z, hBZ45]
  have hcombo :
      336 * exactOrderDistributionInt B 3 +
        66 * exactOrderDistributionInt B 5 +
        60 * exactOrderDistributionInt B 9 +
        150 * exactOrderDistributionInt B 10 +
        66 * exactOrderDistributionInt B 15 +
        60 * exactOrderDistributionInt B 18 +
        60 * exactOrderDistributionInt B 20 +
        150 * exactOrderDistributionInt B 30 +
        60 * exactOrderDistributionInt B 60 +
        60 * exactOrderDistributionInt B 180 = 864 := by
    linarith [hBsum, hBone, hB3z, hB10z, hBZ6, hBZ20, hBZ60]
  clear hBsum hBone hB3z hB10z hBZ6 hBZ20 hBZ45 hBZ60
  have hzeros :
      exactOrderDistributionInt B 2 = 0 ∧
        exactOrderDistributionInt B 4 = 0 ∧
        exactOrderDistributionInt B 5 = 0 ∧
        exactOrderDistributionInt B 10 = 0 ∧
        exactOrderDistributionInt B 15 = 0 ∧
        exactOrderDistributionInt B 20 = 0 ∧
        exactOrderDistributionInt B 30 = 0 ∧
        exactOrderDistributionInt B 60 = 0 := by
    omega
  rcases hzeros with ⟨h2, h4, h5, h10, h15, h20, h30, h60⟩
  omega

end Fuglede
