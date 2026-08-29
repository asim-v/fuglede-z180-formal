import Fuglede.Z180TilingCard36Order6

/-! # Prepared arithmetic context for the cardinality-20 order-10 proof -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Z180Card20TenPrepared (A B : Finset (ZMod 180)) : Prop :=
  exactOrderDistributionInt A 1 + exactOrderDistributionInt A 2 +
      exactOrderDistributionInt A 3 + exactOrderDistributionInt A 4 +
      exactOrderDistributionInt A 5 + exactOrderDistributionInt A 6 +
      exactOrderDistributionInt A 9 + exactOrderDistributionInt A 10 +
      exactOrderDistributionInt A 12 + exactOrderDistributionInt A 15 +
      exactOrderDistributionInt A 18 + exactOrderDistributionInt A 20 +
      exactOrderDistributionInt A 30 + exactOrderDistributionInt A 36 +
      exactOrderDistributionInt A 45 + exactOrderDistributionInt A 60 +
      exactOrderDistributionInt A 90 + exactOrderDistributionInt A 180 = 400 ∧
  exactOrderDistributionInt A 1 = 20 ∧
  0 ≤ exactOrderDistributionInt A 1 ∧
  0 ≤ exactOrderDistributionInt A 3 ∧
  0 ≤ exactOrderDistributionInt A 6 ∧
  0 ≤ exactOrderDistributionInt A 9 ∧
  0 ≤ exactOrderDistributionInt A 12 ∧
  0 ≤ exactOrderDistributionInt A 15 ∧
  0 ≤ exactOrderDistributionInt A 18 ∧
  0 ≤ exactOrderDistributionInt A 30 ∧
  0 ≤ exactOrderDistributionInt A 36 ∧
  0 ≤ exactOrderDistributionInt A 45 ∧
  0 ≤ exactOrderDistributionInt A 90 ∧
  0 ≤ z180ExactOrderTransform A 2 ∧
  0 ≤ z180ExactOrderTransform A 4 ∧
  0 ≤ z180ExactOrderTransform A 5 ∧
  0 ≤ z180ExactOrderTransform A 6 ∧
  0 ≤ z180ExactOrderTransform A 12 ∧
  0 ≤ z180ExactOrderTransform A 20 ∧
  z180ExactOrderTransform A 2 = 0 ∧
  z180ExactOrderTransform A 4 = 0 ∧
  z180ExactOrderTransform A 5 = 0 ∧
  0 < z180ExactOrderTransform A 10 ∧
  exactOrderDistributionInt B 1 + exactOrderDistributionInt B 2 +
      exactOrderDistributionInt B 3 + exactOrderDistributionInt B 4 +
      exactOrderDistributionInt B 5 + exactOrderDistributionInt B 6 +
      exactOrderDistributionInt B 9 + exactOrderDistributionInt B 10 +
      exactOrderDistributionInt B 12 + exactOrderDistributionInt B 15 +
      exactOrderDistributionInt B 18 + exactOrderDistributionInt B 20 +
      exactOrderDistributionInt B 30 + exactOrderDistributionInt B 36 +
      exactOrderDistributionInt B 45 + exactOrderDistributionInt B 60 +
      exactOrderDistributionInt B 90 + exactOrderDistributionInt B 180 = 81 ∧
  exactOrderDistributionInt B 1 = 9 ∧
  0 ≤ exactOrderDistributionInt B 1 ∧
  0 ≤ exactOrderDistributionInt B 2 ∧
  0 ≤ exactOrderDistributionInt B 3 ∧
  0 ≤ exactOrderDistributionInt B 4 ∧
  0 ≤ exactOrderDistributionInt B 5 ∧
  0 ≤ exactOrderDistributionInt B 6 ∧
  0 ≤ exactOrderDistributionInt B 9 ∧
  0 ≤ exactOrderDistributionInt B 10 ∧
  0 ≤ exactOrderDistributionInt B 12 ∧
  0 ≤ exactOrderDistributionInt B 15 ∧
  0 ≤ exactOrderDistributionInt B 18 ∧
  0 ≤ exactOrderDistributionInt B 20 ∧
  0 ≤ exactOrderDistributionInt B 30 ∧
  0 ≤ exactOrderDistributionInt B 45 ∧
  0 ≤ exactOrderDistributionInt B 60 ∧
  0 ≤ exactOrderDistributionInt B 90 ∧
  0 ≤ exactOrderDistributionInt B 180 ∧
  0 ≤ z180ExactOrderTransform B 6 ∧
  0 ≤ z180ExactOrderTransform B 10 ∧
  0 ≤ z180ExactOrderTransform B 12 ∧
  0 ≤ z180ExactOrderTransform B 15 ∧
  0 ≤ z180ExactOrderTransform B 18 ∧
  0 ≤ z180ExactOrderTransform B 20 ∧
  0 ≤ z180ExactOrderTransform B 30 ∧
  0 ≤ z180ExactOrderTransform B 36 ∧
  0 ≤ z180ExactOrderTransform B 45 ∧
  0 ≤ z180ExactOrderTransform B 60 ∧
  0 ≤ z180ExactOrderTransform B 90 ∧
  0 ≤ z180ExactOrderTransform B 180 ∧
  z180ExactOrderTransform B 3 = 0 ∧
  z180ExactOrderTransform B 9 = 0 ∧
  z180ExactOrderTransform B 10 = 0

structure Z180Card20TenFacts (A B : Finset (ZMod 180)) : Prop where
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
  AC1 : 0 ≤ exactOrderDistributionInt A 1
  AC3 : 0 ≤ exactOrderDistributionInt A 3
  AC6 : 0 ≤ exactOrderDistributionInt A 6
  AC9 : 0 ≤ exactOrderDistributionInt A 9
  AC12 : 0 ≤ exactOrderDistributionInt A 12
  AC15 : 0 ≤ exactOrderDistributionInt A 15
  AC18 : 0 ≤ exactOrderDistributionInt A 18
  AC30 : 0 ≤ exactOrderDistributionInt A 30
  AC36 : 0 ≤ exactOrderDistributionInt A 36
  AC45 : 0 ≤ exactOrderDistributionInt A 45
  AC90 : 0 ≤ exactOrderDistributionInt A 90
  AT2 : 0 ≤ z180ExactOrderTransform A 2
  AT4 : 0 ≤ z180ExactOrderTransform A 4
  AT5 : 0 ≤ z180ExactOrderTransform A 5
  AT6 : 0 ≤ z180ExactOrderTransform A 6
  AT12 : 0 ≤ z180ExactOrderTransform A 12
  AT20 : 0 ≤ z180ExactOrderTransform A 20
  A2z : z180ExactOrderTransform A 2 = 0
  A4z : z180ExactOrderTransform A 4 = 0
  A5z : z180ExactOrderTransform A 5 = 0
  A10p : 0 < z180ExactOrderTransform A 10
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
  BC1 : 0 ≤ exactOrderDistributionInt B 1
  BC2 : 0 ≤ exactOrderDistributionInt B 2
  BC3 : 0 ≤ exactOrderDistributionInt B 3
  BC4 : 0 ≤ exactOrderDistributionInt B 4
  BC5 : 0 ≤ exactOrderDistributionInt B 5
  BC6 : 0 ≤ exactOrderDistributionInt B 6
  BC9 : 0 ≤ exactOrderDistributionInt B 9
  BC10 : 0 ≤ exactOrderDistributionInt B 10
  BC12 : 0 ≤ exactOrderDistributionInt B 12
  BC15 : 0 ≤ exactOrderDistributionInt B 15
  BC18 : 0 ≤ exactOrderDistributionInt B 18
  BC20 : 0 ≤ exactOrderDistributionInt B 20
  BC30 : 0 ≤ exactOrderDistributionInt B 30
  BC45 : 0 ≤ exactOrderDistributionInt B 45
  BC60 : 0 ≤ exactOrderDistributionInt B 60
  BC90 : 0 ≤ exactOrderDistributionInt B 90
  BC180 : 0 ≤ exactOrderDistributionInt B 180
  BT6 : 0 ≤ z180ExactOrderTransform B 6
  BT10 : 0 ≤ z180ExactOrderTransform B 10
  BT12 : 0 ≤ z180ExactOrderTransform B 12
  BT15 : 0 ≤ z180ExactOrderTransform B 15
  BT18 : 0 ≤ z180ExactOrderTransform B 18
  BT20 : 0 ≤ z180ExactOrderTransform B 20
  BT30 : 0 ≤ z180ExactOrderTransform B 30
  BT36 : 0 ≤ z180ExactOrderTransform B 36
  BT45 : 0 ≤ z180ExactOrderTransform B 45
  BT60 : 0 ≤ z180ExactOrderTransform B 60
  BT90 : 0 ≤ z180ExactOrderTransform B 90
  BT180 : 0 ≤ z180ExactOrderTransform B 180
  B3z : z180ExactOrderTransform B 3 = 0
  B9z : z180ExactOrderTransform B 9 = 0
  B10z : z180ExactOrderTransform B 10 = 0

theorem z180_card20_prepare_ten
    {A B : Finset (ZMod 180)}
    (hAcard : A.card = 20) (hBcard : B.card = 9)
    (hA2 : z180ExactOrderTransform A 2 = 0)
    (hA4 : z180ExactOrderTransform A 4 = 0)
    (hA5 : z180ExactOrderTransform A 5 = 0)
    (hB3 : z180ExactOrderTransform B 3 = 0)
    (hB9 : z180ExactOrderTransform B 9 = 0)
    (hcover10 : z180ExactOrderTransform A 10 = 0 ∨
      z180ExactOrderTransform B 10 = 0)
    (hA10ne : z180ExactOrderTransform A 10 ≠ 0) :
    Z180Card20TenFacts A B := by
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
  have hA10nonneg := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity A) (e := 10) (by norm_num)
  have hA10pos := lt_of_le_of_ne hA10nonneg (Ne.symm hA10ne)
  have hB10 := hcover10.resolve_left hA10ne
  exact ⟨hAsum, hA1,
    exactOrderDistributionInt_nonneg A 1,
    exactOrderDistributionInt_nonneg A 3,
    exactOrderDistributionInt_nonneg A 6,
    exactOrderDistributionInt_nonneg A 9,
    exactOrderDistributionInt_nonneg A 12,
    exactOrderDistributionInt_nonneg A 15,
    exactOrderDistributionInt_nonneg A 18,
    exactOrderDistributionInt_nonneg A 30,
    exactOrderDistributionInt_nonneg A 36,
    exactOrderDistributionInt_nonneg A 45,
    exactOrderDistributionInt_nonneg A 90,
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 2) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 4) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 5) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 6) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 12) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity A) (e := 20) (by norm_num),
    hA2, hA4, hA5, hA10pos, hBsum, hB1,
    exactOrderDistributionInt_nonneg B 1,
    exactOrderDistributionInt_nonneg B 2,
    exactOrderDistributionInt_nonneg B 3,
    exactOrderDistributionInt_nonneg B 4,
    exactOrderDistributionInt_nonneg B 5,
    exactOrderDistributionInt_nonneg B 6,
    exactOrderDistributionInt_nonneg B 9,
    exactOrderDistributionInt_nonneg B 10,
    exactOrderDistributionInt_nonneg B 12,
    exactOrderDistributionInt_nonneg B 15,
    exactOrderDistributionInt_nonneg B 18,
    exactOrderDistributionInt_nonneg B 20,
    exactOrderDistributionInt_nonneg B 30,
    exactOrderDistributionInt_nonneg B 45,
    exactOrderDistributionInt_nonneg B 60,
    exactOrderDistributionInt_nonneg B 90,
    exactOrderDistributionInt_nonneg B 180,
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 6) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 10) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 12) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 15) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 18) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 20) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 30) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 36) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 45) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 60) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 90) (by norm_num),
    z180ExactOrderTransform_nonneg (z180RamanujanIdentity B) (e := 180) (by norm_num),
    hB3, hB9, hB10⟩

end Fuglede
