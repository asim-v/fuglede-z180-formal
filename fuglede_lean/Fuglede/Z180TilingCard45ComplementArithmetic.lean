import Fuglede.Z180TilingCard36Order6

/-! # Four-point complement arithmetic for the cardinality-45 case -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z180_card4_pattern_of_zeros_two_four_fifteen
    {B : Finset (ZMod 180)} (hcard : B.card = 4)
    (h2 : z180ExactOrderTransform B 2 = 0)
    (h4 : z180ExactOrderTransform B 4 = 0)
    (h15 : z180ExactOrderTransform B 15 = 0) :
    (z180ExactOrderTransform B 30 ≠ 0 ∧
      z180ExactOrderTransform B 45 ≠ 0 ∧
      z180ExactOrderTransform B 60 ≠ 0 ∧
      z180ExactOrderTransform B 90 ≠ 0 ∧
      z180ExactOrderTransform B 180 ≠ 0) ∧
    (z180ExactOrderTransform B 36 = 0 →
      z180ExactOrderTransform B 6 ≠ 0 ∧
      z180ExactOrderTransform B 18 ≠ 0 ∧
      z180ExactOrderTransform B 20 ≠ 0) ∧
    (z180ExactOrderTransform B 36 ≠ 0 →
      z180ExactOrderTransform B 10 = 0 →
      z180ExactOrderTransform B 6 ≠ 0 ∧
      z180ExactOrderTransform B 20 ≠ 0) ∧
    (z180ExactOrderTransform B 36 ≠ 0 →
      z180ExactOrderTransform B 10 ≠ 0 →
      z180ExactOrderTransform B 12 ≠ 0) := by
  have hsum := z180_sum_exactOrderDistributionInt B
  have h1 := exactOrderDistributionInt_one B
  have hC2 := exactOrderDistributionInt_nonneg B 2
  have hC3 := exactOrderDistributionInt_nonneg B 3
  have hC4 := exactOrderDistributionInt_nonneg B 4
  have hC5 := exactOrderDistributionInt_nonneg B 5
  have hC6 := exactOrderDistributionInt_nonneg B 6
  have hC9 := exactOrderDistributionInt_nonneg B 9
  have hC10 := exactOrderDistributionInt_nonneg B 10
  have hC12 := exactOrderDistributionInt_nonneg B 12
  have hC15 := exactOrderDistributionInt_nonneg B 15
  have hC18 := exactOrderDistributionInt_nonneg B 18
  have hC20 := exactOrderDistributionInt_nonneg B 20
  have hC30 := exactOrderDistributionInt_nonneg B 30
  have hC36 := exactOrderDistributionInt_nonneg B 36
  have hC45 := exactOrderDistributionInt_nonneg B 45
  have hC60 := exactOrderDistributionInt_nonneg B 60
  have hC90 := exactOrderDistributionInt_nonneg B 90
  have hC180 := exactOrderDistributionInt_nonneg B 180
  have hT10 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity B) (e := 10) (by norm_num)
  have hT36 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity B) (e := 36) (by norm_num)
  have hcardCast : (B.card : Int) = 4 := by exact_mod_cast hcard
  have hcardSqCast : ((B.card ^ 2 : Nat) : Int) = 16 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  simp only [z180ExactOrderTransform] at h2 h4 h15
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      intro hx <;> simp only [z180ExactOrderTransform] at hx <;> linarith
  · intro h36
    simp only [z180ExactOrderTransform] at h36
    refine ⟨?_, ?_, ?_⟩ <;>
      intro hx <;> simp only [z180ExactOrderTransform] at hx <;> linarith
  · intro h36 h10
    simp only [z180ExactOrderTransform] at h36 h10 hT36
    have h36pos : 0 <
        exactOrderDistributionInt B 1 * 12 +
          exactOrderDistributionInt B 2 * (-12) +
          exactOrderDistributionInt B 3 * (-6) +
          exactOrderDistributionInt B 4 * 0 +
          exactOrderDistributionInt B 5 * 12 +
          exactOrderDistributionInt B 6 * 6 +
          exactOrderDistributionInt B 9 * 0 +
          exactOrderDistributionInt B 10 * (-12) +
          exactOrderDistributionInt B 12 * 0 +
          exactOrderDistributionInt B 15 * (-6) +
          exactOrderDistributionInt B 18 * 0 +
          exactOrderDistributionInt B 20 * 0 +
          exactOrderDistributionInt B 30 * 6 +
          exactOrderDistributionInt B 36 * 0 +
          exactOrderDistributionInt B 45 * 0 +
          exactOrderDistributionInt B 60 * 0 +
          exactOrderDistributionInt B 90 * 0 +
          exactOrderDistributionInt B 180 * 0 :=
      lt_of_le_of_ne hT36 (Ne.symm h36)
    refine ⟨?_, ?_⟩
    · intro hx
      simp only [z180ExactOrderTransform] at hx
      linarith
    · intro hx
      simp only [z180ExactOrderTransform] at hx
      have hfrac :
          3 * exactOrderDistributionInt B 36 -
              3 * exactOrderDistributionInt B 6 -
              3 * exactOrderDistributionInt B 2 = 20 := by
        linarith
      omega
  · intro h36 h10 h12
    simp only [z180ExactOrderTransform] at h36 h10 h12 hT10 hT36
    have h36pos := lt_of_le_of_ne hT36 (Ne.symm h36)
    have h10pos := lt_of_le_of_ne hT10 (Ne.symm h10)
    linarith

theorem z180_card4_pattern_of_zeros_two_four_forty_five
    {B : Finset (ZMod 180)} (hcard : B.card = 4)
    (h2 : z180ExactOrderTransform B 2 = 0)
    (h4 : z180ExactOrderTransform B 4 = 0)
    (h45 : z180ExactOrderTransform B 45 = 0) :
    (z180ExactOrderTransform B 15 ≠ 0 ∧
      z180ExactOrderTransform B 90 ≠ 0 ∧
      z180ExactOrderTransform B 180 ≠ 0) ∧
    (z180ExactOrderTransform B 18 = 0 →
      z180ExactOrderTransform B 10 ≠ 0 ∧
      z180ExactOrderTransform B 30 ≠ 0 ∧
      z180ExactOrderTransform B 36 ≠ 0) ∧
    (z180ExactOrderTransform B 36 = 0 →
      z180ExactOrderTransform B 18 ≠ 0 ∧
      z180ExactOrderTransform B 20 ≠ 0 ∧
      z180ExactOrderTransform B 60 ≠ 0) := by
  have hsum := z180_sum_exactOrderDistributionInt B
  have h1 := exactOrderDistributionInt_one B
  have hC2 := exactOrderDistributionInt_nonneg B 2
  have hC3 := exactOrderDistributionInt_nonneg B 3
  have hC4 := exactOrderDistributionInt_nonneg B 4
  have hC5 := exactOrderDistributionInt_nonneg B 5
  have hC6 := exactOrderDistributionInt_nonneg B 6
  have hC9 := exactOrderDistributionInt_nonneg B 9
  have hC10 := exactOrderDistributionInt_nonneg B 10
  have hC12 := exactOrderDistributionInt_nonneg B 12
  have hC15 := exactOrderDistributionInt_nonneg B 15
  have hC18 := exactOrderDistributionInt_nonneg B 18
  have hC20 := exactOrderDistributionInt_nonneg B 20
  have hC30 := exactOrderDistributionInt_nonneg B 30
  have hC36 := exactOrderDistributionInt_nonneg B 36
  have hC45 := exactOrderDistributionInt_nonneg B 45
  have hC60 := exactOrderDistributionInt_nonneg B 60
  have hC90 := exactOrderDistributionInt_nonneg B 90
  have hC180 := exactOrderDistributionInt_nonneg B 180
  have hcardCast : (B.card : Int) = 4 := by exact_mod_cast hcard
  have hcardSqCast : ((B.card ^ 2 : Nat) : Int) = 16 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  simp only [z180ExactOrderTransform] at h2 h4 h45
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;>
      intro hx <;> simp only [z180ExactOrderTransform] at hx <;> linarith
  · intro h18
    simp only [z180ExactOrderTransform] at h18
    refine ⟨?_, ?_, ?_⟩ <;>
      intro hx <;> simp only [z180ExactOrderTransform] at hx <;> linarith
  · intro h36
    simp only [z180ExactOrderTransform] at h36
    refine ⟨?_, ?_, ?_⟩ <;>
      intro hx <;> simp only [z180ExactOrderTransform] at hx <;> linarith

#print axioms z180_card4_pattern_of_zeros_two_four_fifteen
#print axioms z180_card4_pattern_of_zeros_two_four_forty_five

end Fuglede
