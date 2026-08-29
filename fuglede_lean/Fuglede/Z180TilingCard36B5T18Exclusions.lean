import Fuglede.Z180TilingCard36Order12

namespace Fuglede

set_option maxHeartbeats 0

private theorem int_three_mul_add_three_mul_ne_ten (x y : Int) :
    3 * x + 3 * y ≠ 10 := by omega
private theorem int_two_mul_ne_twenty_five (x : Int) : 2 * x ≠ 25 := by omega
private theorem int_three_mul_ne_ten (x : Int) : 3 * x ≠ 10 := by omega

/-- The five large-order exclusions forced by transform zeros at orders 5 and 18. -/
theorem z180_card_five_exclusions_of_transform_five_eighteen_zero
    {B : Finset (ZMod 180)} (hcard : B.card = 5)
    (h5 : z180ExactOrderTransform B 5 = 0)
    (h18 : z180ExactOrderTransform B 18 = 0) :
    z180ExactOrderTransform B 30 ≠ 0 ∧
    z180ExactOrderTransform B 45 ≠ 0 ∧
    z180ExactOrderTransform B 60 ≠ 0 ∧
    z180ExactOrderTransform B 90 ≠ 0 ∧
    z180ExactOrderTransform B 180 ≠ 0 := by
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
  have hcardCast : (B.card : Int) = 5 := by exact_mod_cast hcard
  have hcardSqCast : ((B.card ^ 2 : Nat) : Int) = 25 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  simp only [z180ExactOrderTransform] at h5 h18
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx
    simp only [z180ExactOrderTransform] at hx
    have hdiv : 3 * exactOrderDistributionInt B 5 +
        3 * exactOrderDistributionInt B 10 = 10 := by linarith
    exact int_three_mul_add_three_mul_ne_ten _ _ hdiv
  · intro hx
    simp only [z180ExactOrderTransform] at hx
    have hdiv : 2 * exactOrderDistributionInt B 20 = 25 := by linarith
    exact int_two_mul_ne_twenty_five _ hdiv
  · intro hx
    simp only [z180ExactOrderTransform] at hx
    have hdiv : 3 * exactOrderDistributionInt B 5 = 10 := by linarith
    exact int_three_mul_ne_ten _ hdiv
  · intro hx
    simp only [z180ExactOrderTransform] at hx
    linarith
  · intro hx
    simp only [z180ExactOrderTransform] at hx
    linarith

#print axioms z180_card_five_exclusions_of_transform_five_eighteen_zero

end Fuglede
