import Fuglede.Z180TilingCard20TenAggregate

/-! # Prepared arithmetic context for the cardinality-20 order-20 proof -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Z180Card20TwentyFacts (A B : Finset (ZMod 180)) : Prop where
  Asum :
    exactOrderDistributionInt A 1 + exactOrderDistributionInt A 2 +
        exactOrderDistributionInt A 3 + exactOrderDistributionInt A 4 +
        exactOrderDistributionInt A 5 + exactOrderDistributionInt A 6 +
        exactOrderDistributionInt A 9 + exactOrderDistributionInt A 10 +
        exactOrderDistributionInt A 12 + exactOrderDistributionInt A 15 +
        exactOrderDistributionInt A 18 + exactOrderDistributionInt A 20 +
        exactOrderDistributionInt A 30 + exactOrderDistributionInt A 36 +
        exactOrderDistributionInt A 45 + exactOrderDistributionInt A 60 +
        exactOrderDistributionInt A 90 + exactOrderDistributionInt A 180 = 400
  Aone : exactOrderDistributionInt A 1 = 20
  AC3 : 0 ≤ exactOrderDistributionInt A 3
  AC6 : 0 ≤ exactOrderDistributionInt A 6
  AC9 : 0 ≤ exactOrderDistributionInt A 9
  AC18 : 0 ≤ exactOrderDistributionInt A 18
  AT4 : 0 ≤ z180ExactOrderTransform A 4
  A2z : z180ExactOrderTransform A 2 = 0
  A5z : z180ExactOrderTransform A 5 = 0
  A10z : z180ExactOrderTransform A 10 = 0
  A20p : 0 < z180ExactOrderTransform A 20
  Bsum :
    exactOrderDistributionInt B 1 + exactOrderDistributionInt B 2 +
        exactOrderDistributionInt B 3 + exactOrderDistributionInt B 4 +
        exactOrderDistributionInt B 5 + exactOrderDistributionInt B 6 +
        exactOrderDistributionInt B 9 + exactOrderDistributionInt B 10 +
        exactOrderDistributionInt B 12 + exactOrderDistributionInt B 15 +
        exactOrderDistributionInt B 18 + exactOrderDistributionInt B 20 +
        exactOrderDistributionInt B 30 + exactOrderDistributionInt B 36 +
        exactOrderDistributionInt B 45 + exactOrderDistributionInt B 60 +
        exactOrderDistributionInt B 90 + exactOrderDistributionInt B 180 = 81
  Bone : exactOrderDistributionInt B 1 = 9
  BC2 : 0 ≤ exactOrderDistributionInt B 2
  BC3 : 0 ≤ exactOrderDistributionInt B 3
  BC4 : 0 ≤ exactOrderDistributionInt B 4
  BC5 : 0 ≤ exactOrderDistributionInt B 5
  BC6 : 0 ≤ exactOrderDistributionInt B 6
  BC9 : 0 ≤ exactOrderDistributionInt B 9
  BC10 : 0 ≤ exactOrderDistributionInt B 10
  BC12 : 0 ≤ exactOrderDistributionInt B 12
  BC15 : 0 ≤ exactOrderDistributionInt B 15
  BC20 : 0 ≤ exactOrderDistributionInt B 20
  BC30 : 0 ≤ exactOrderDistributionInt B 30
  BC60 : 0 ≤ exactOrderDistributionInt B 60
  BC90 : 0 ≤ exactOrderDistributionInt B 90
  BT6 : 0 ≤ z180ExactOrderTransform B 6
  B3z : z180ExactOrderTransform B 3 = 0
  B9z : z180ExactOrderTransform B 9 = 0
  B20z : z180ExactOrderTransform B 20 = 0

theorem z180_card20_prepare_twenty
    {A B : Finset (ZMod 180)}
    (hAcard : A.card = 20) (hBcard : B.card = 9)
    (hA2 : z180ExactOrderTransform A 2 = 0)
    (hA5 : z180ExactOrderTransform A 5 = 0)
    (hA10 : z180ExactOrderTransform A 10 = 0)
    (hB3 : z180ExactOrderTransform B 3 = 0)
    (hB9 : z180ExactOrderTransform B 9 = 0)
    (hcover20 : z180ExactOrderTransform A 20 = 0 ∨
      z180ExactOrderTransform B 20 = 0)
    (hA20ne : z180ExactOrderTransform A 20 ≠ 0) :
    Z180Card20TwentyFacts A B := by
  have hAsum := z180_sum_exactOrderDistributionInt A
  have hA1 := exactOrderDistributionInt_one A
  have hBsum := z180_sum_exactOrderDistributionInt B
  have hB1 := exactOrderDistributionInt_one B
  have hAcardCast : (A.card : Int) = 20 := by exact_mod_cast hAcard
  have hAcardSqCast : ((A.card ^ 2 : Nat) : Int) = 400 := by
    rw [hAcard]
    norm_num
  have hBcardCast : (B.card : Int) = 9 := by exact_mod_cast hBcard
  have hBcardSqCast : ((B.card ^ 2 : Nat) : Int) = 81 := by
    rw [hBcard]
    norm_num
  rw [hAcardCast] at hA1
  rw [hAcardSqCast] at hAsum
  rw [hBcardCast] at hB1
  rw [hBcardSqCast] at hBsum
  have hA20nonneg := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity A) (e := 20) (by norm_num)
  have hA20pos := lt_of_le_of_ne hA20nonneg (Ne.symm hA20ne)
  have hB20 := hcover20.resolve_left hA20ne
  exact ⟨hAsum, hA1,
    exactOrderDistributionInt_nonneg A 3,
    exactOrderDistributionInt_nonneg A 6,
    exactOrderDistributionInt_nonneg A 9,
    exactOrderDistributionInt_nonneg A 18,
    z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 4) (by norm_num),
    hA2, hA5, hA10, hA20pos,
    hBsum, hB1,
    exactOrderDistributionInt_nonneg B 2,
    exactOrderDistributionInt_nonneg B 3,
    exactOrderDistributionInt_nonneg B 4,
    exactOrderDistributionInt_nonneg B 5,
    exactOrderDistributionInt_nonneg B 6,
    exactOrderDistributionInt_nonneg B 9,
    exactOrderDistributionInt_nonneg B 10,
    exactOrderDistributionInt_nonneg B 12,
    exactOrderDistributionInt_nonneg B 15,
    exactOrderDistributionInt_nonneg B 20,
    exactOrderDistributionInt_nonneg B 30,
    exactOrderDistributionInt_nonneg B 60,
    exactOrderDistributionInt_nonneg B 90,
    z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity B) (e := 6) (by norm_num),
    hB3, hB9, hB20⟩

end Fuglede
