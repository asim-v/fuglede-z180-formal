import Fuglede.Z180TilingCard36Order6

/-! # Forty-five-point factor arithmetic -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card45_transform_fifteen_zero_of_three_cases
    {A : Finset (ZMod 180)} (hcard : A.card = 45)
    (h3 : z180ExactOrderTransform A 3 = 0)
    (h5 : z180ExactOrderTransform A 5 = 0)
    (h9 : z180ExactOrderTransform A 9 = 0)
    (h30 : z180ExactOrderTransform A 30 = 0)
    (h45 : z180ExactOrderTransform A 45 = 0)
    (h60 : z180ExactOrderTransform A 60 = 0)
    (h90 : z180ExactOrderTransform A 90 = 0)
    (h180 : z180ExactOrderTransform A 180 = 0)
    (hcase :
      (z180ExactOrderTransform A 6 = 0 ∧
        z180ExactOrderTransform A 18 = 0 ∧
        z180ExactOrderTransform A 20 = 0) ∨
      (z180ExactOrderTransform A 6 = 0 ∧
        z180ExactOrderTransform A 20 = 0 ∧
        z180ExactOrderTransform A 36 = 0) ∨
      (z180ExactOrderTransform A 10 = 0 ∧
        z180ExactOrderTransform A 12 = 0 ∧
        z180ExactOrderTransform A 36 = 0)) :
    z180ExactOrderTransform A 15 = 0 := by
  have hsum := z180_sum_exactOrderDistributionInt A
  have h1 := exactOrderDistributionInt_one A
  have hC2 := exactOrderDistributionInt_nonneg A 2
  have hC3 := exactOrderDistributionInt_nonneg A 3
  have hC4 := exactOrderDistributionInt_nonneg A 4
  have hC5 := exactOrderDistributionInt_nonneg A 5
  have hC6 := exactOrderDistributionInt_nonneg A 6
  have hC9 := exactOrderDistributionInt_nonneg A 9
  have hC10 := exactOrderDistributionInt_nonneg A 10
  have hC12 := exactOrderDistributionInt_nonneg A 12
  have hC15 := exactOrderDistributionInt_nonneg A 15
  have hC18 := exactOrderDistributionInt_nonneg A 18
  have hC20 := exactOrderDistributionInt_nonneg A 20
  have hC30 := exactOrderDistributionInt_nonneg A 30
  have hC36 := exactOrderDistributionInt_nonneg A 36
  have hC45 := exactOrderDistributionInt_nonneg A 45
  have hC60 := exactOrderDistributionInt_nonneg A 60
  have hC90 := exactOrderDistributionInt_nonneg A 90
  have hC180 := exactOrderDistributionInt_nonneg A 180
  have hT10 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity A) (e := 10) (by norm_num)
  have hcardCast : (A.card : Int) = 45 := by exact_mod_cast hcard
  have hcardSqCast : ((A.card ^ 2 : Nat) : Int) = 2025 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  rcases hcase with hcase | hcase | hcase
  all_goals
    rcases hcase with ⟨ha, hb, hc⟩
    simp only [z180ExactOrderTransform] at h3 h5 h9 h30 h45 h60 h90 h180
    simp only [z180ExactOrderTransform] at ha hb hc hT10 ⊢
    linarith

theorem z180_card45_transform_forty_five_zero_of_three_cases
    {A : Finset (ZMod 180)} (hcard : A.card = 45)
    (h3 : z180ExactOrderTransform A 3 = 0)
    (h5 : z180ExactOrderTransform A 5 = 0)
    (h9 : z180ExactOrderTransform A 9 = 0)
    (h15 : z180ExactOrderTransform A 15 = 0)
    (h90 : z180ExactOrderTransform A 90 = 0)
    (h180 : z180ExactOrderTransform A 180 = 0)
    (hcase :
      (z180ExactOrderTransform A 18 = 0 ∧
        z180ExactOrderTransform A 36 = 0) ∨
      (z180ExactOrderTransform A 10 = 0 ∧
        z180ExactOrderTransform A 30 = 0 ∧
        z180ExactOrderTransform A 36 = 0) ∨
      (z180ExactOrderTransform A 18 = 0 ∧
        z180ExactOrderTransform A 20 = 0 ∧
        z180ExactOrderTransform A 60 = 0)) :
    z180ExactOrderTransform A 45 = 0 := by
  have hsum := z180_sum_exactOrderDistributionInt A
  have h1 := exactOrderDistributionInt_one A
  have hC2 := exactOrderDistributionInt_nonneg A 2
  have hC3 := exactOrderDistributionInt_nonneg A 3
  have hC4 := exactOrderDistributionInt_nonneg A 4
  have hC5 := exactOrderDistributionInt_nonneg A 5
  have hC6 := exactOrderDistributionInt_nonneg A 6
  have hC9 := exactOrderDistributionInt_nonneg A 9
  have hC10 := exactOrderDistributionInt_nonneg A 10
  have hC12 := exactOrderDistributionInt_nonneg A 12
  have hC15 := exactOrderDistributionInt_nonneg A 15
  have hC18 := exactOrderDistributionInt_nonneg A 18
  have hC20 := exactOrderDistributionInt_nonneg A 20
  have hC30 := exactOrderDistributionInt_nonneg A 30
  have hC36 := exactOrderDistributionInt_nonneg A 36
  have hC45 := exactOrderDistributionInt_nonneg A 45
  have hC60 := exactOrderDistributionInt_nonneg A 60
  have hC90 := exactOrderDistributionInt_nonneg A 90
  have hC180 := exactOrderDistributionInt_nonneg A 180
  have hT10 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity A) (e := 10) (by norm_num)
  have hT30 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity A) (e := 30) (by norm_num)
  have hcardCast : (A.card : Int) = 45 := by exact_mod_cast hcard
  have hcardSqCast : ((A.card ^ 2 : Nat) : Int) = 2025 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  rcases hcase with hcase | hcase | hcase
  · rcases hcase with ⟨ha, hb⟩
    simp only [z180ExactOrderTransform] at h3 h5 h9 h15 h90 h180
    simp only [z180ExactOrderTransform] at ha hb hT10 hT30 ⊢
    linarith
  all_goals
    rcases hcase with ⟨ha, hb, hc⟩
    simp only [z180ExactOrderTransform] at h3 h5 h9 h15 h90 h180
    simp only [z180ExactOrderTransform] at ha hb hc hT10 hT30 ⊢
    linarith

#print axioms z180_card45_transform_fifteen_zero_of_three_cases
#print axioms z180_card45_transform_forty_five_zero_of_three_cases

end Fuglede
