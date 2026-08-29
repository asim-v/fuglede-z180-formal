import Fuglede.Z180TilingCard36B5T12Primary

namespace Fuglede

set_option maxHeartbeats 0

private theorem int_two_mul_add_two_mul_ne_fifteen (x y : Int) :
    2 * x + 2 * y ≠ 15 := by omega

/-- The remaining five-point exclusions after the order-10 branch is selected. -/
theorem z180_card_five_secondary_exclusions_five_twelve_ten
    {B : Finset (ZMod 180)} (hcard : B.card = 5)
    (h5 : z180ExactOrderTransform B 5 = 0)
    (h12 : z180ExactOrderTransform B 12 = 0)
    (h10 : z180ExactOrderTransform B 10 = 0) :
    z180ExactOrderTransform B 15 ≠ 0 ∧
    (z180ExactOrderTransform B 18 = 0 →
      z180ExactOrderTransform B 36 ≠ 0 ∧
      z180ExactOrderTransform B 45 ≠ 0) := by
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
  have hE5 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity B) (e := 5) (by norm_num)
  have hE10 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity B) (e := 10) (by norm_num)
  have hE12 := z180ExactOrderTransform_nonneg
    (z180RamanujanIdentity B) (e := 12) (by norm_num)
  have hcardCast : (B.card : Int) = 5 := by exact_mod_cast hcard
  have hcardSqCast : ((B.card ^ 2 : Nat) : Int) = 25 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  simp only [z180ExactOrderTransform] at h5 h10 h12 hE5 hE10 hE12
  constructor
  · intro h15
    simp only [z180ExactOrderTransform] at h15
    have hdiv : 2 * exactOrderDistributionInt B 5 +
        2 * exactOrderDistributionInt B 15 = 15 := by linarith
    exact int_two_mul_add_two_mul_ne_fifteen _ _ hdiv
  · intro h18
    simp only [z180ExactOrderTransform] at h18
    constructor <;> intro hx <;>
      simp only [z180ExactOrderTransform] at hx <;> linarith

#print axioms z180_card_five_secondary_exclusions_five_twelve_ten

end Fuglede
