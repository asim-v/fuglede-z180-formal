import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180ExactOrderTransform

/-!
# Strict order-three and order-nine rows at modulus 180

These are the two prime-power strictness lemmas needed by the cardinality-ten
exact-order certificate.  They live in a separate module so the previously
audited transform table remains byte-for-byte stable.
-/

namespace Fuglede

open Polynomial

private theorem z180_transform_ne_zero_three
    {X : Finset (ZMod 180)} (hnot : ¬ 3 ∣ X.card) :
    z180ExactOrderTransform X 3 ≠ 0 := by
  intro hzero
  have hidentity := z180RamanujanIdentity_all X
  have henergy : exactOrderFourierEnergy X 3 = 0 := by
    have h := hidentity 3 (by norm_num)
    rw [hzero] at h
    norm_num at h
    exact h.symm
  have horbit :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X 3).mp henergy
  have horder : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  exact hnot (prime_dvd_card_of_cyclotomicZero (by norm_num) X 60 horder
    (horbit 60 horder))

private theorem z180_transform_ne_zero_nine
    {X : Finset (ZMod 180)} (hnot : ¬ 3 ∣ X.card) :
    z180ExactOrderTransform X 9 ≠ 0 := by
  intro hzero
  have hidentity := z180RamanujanIdentity_all X
  have henergy : exactOrderFourierEnergy X 9 = 0 := by
    have h := hidentity 9 (by norm_num)
    rw [hzero] at h
    norm_num at h
    exact h.symm
  have horbit :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X 9).mp henergy
  have horder : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have hcyclo := horbit 20 horder
  have hdiv : cyclotomic (3 ^ (1 + 1)) Int ∣ maskPolynomial 180 X := by
    simpa [CyclotomicZero, horder] using hcyclo
  exact hnot (prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
    (by norm_num) 1 X hdiv)

theorem z180ExactOrderTransform_pos_three
    {X : Finset (ZMod 180)} (hnot : ¬ 3 ∣ X.card) :
    0 < z180ExactOrderTransform X 3 := by
  exact lt_of_le_of_ne
    (z180ExactOrderTransform_nonneg (z180RamanujanIdentity_all X) (by norm_num))
    (Ne.symm (z180_transform_ne_zero_three hnot))

theorem z180ExactOrderTransform_pos_nine
    {X : Finset (ZMod 180)} (hnot : ¬ 3 ∣ X.card) :
    0 < z180ExactOrderTransform X 9 := by
  exact lt_of_le_of_ne
    (z180ExactOrderTransform_nonneg (z180RamanujanIdentity_all X) (by norm_num))
    (Ne.symm (z180_transform_ne_zero_nine hnot))

end Fuglede
