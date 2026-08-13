import Fuglede.CRT180RamanujanClosure
import Fuglede.Z180K18ForcedTypedAdapter
import Mathlib.Tactic

/-!
# Forced Phi3 and Phi9 zeros at cardinality eighteen

This is the small typed endpoint of the sharded arithmetic certificate.  The
certificate proves exact-order transform zeros; the unconditional Ramanujan
identity turns them into Fourier-energy zeros, hence cyclotomic zeros on both
sides of a spectral pair.
-/

namespace Fuglede

/-- Unconditional form of the four transform zeros. -/
theorem z180_k18_forced_transform_zeros_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    z180ExactOrderTransform A 3 = 0 ∧
      z180ExactOrderTransform A 9 = 0 ∧
      z180ExactOrderTransform L 3 = 0 ∧
      z180ExactOrderTransform L 9 = 0 := by
  exact z180_k18_forced_transform_zeros_of_spectral_of_ramanujan
    hSpec hcard (z180RamanujanIdentity A) (z180RamanujanIdentity L)

private theorem z180_k18_zero_at_order_three_of_transform_zero
    {X : Finset (ZMod 180)}
    (hzero : z180ExactOrderTransform X 3 = 0) :
    ∀ d : ZMod 180, frequencyOrder 180 d = 3 → CyclotomicZero 180 X d := by
  have hidentity := z180RamanujanIdentity X
  have henergy : exactOrderFourierEnergy X 3 = 0 := by
    have h := hidentity 3 (by norm_num)
    rw [hzero] at h
    norm_num at h
    exact h.symm
  exact (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X 3).mp henergy

private theorem z180_k18_zero_at_order_nine_of_transform_zero
    {X : Finset (ZMod 180)}
    (hzero : z180ExactOrderTransform X 9 = 0) :
    ∀ d : ZMod 180, frequencyOrder 180 d = 9 → CyclotomicZero 180 X d := by
  have hidentity := z180RamanujanIdentity X
  have henergy : exactOrderFourierEnergy X 9 = 0 := by
    have h := hidentity 9 (by norm_num)
    rw [hzero] at h
    norm_num at h
    exact h.symm
  exact (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X 9).mp henergy

/-- Orbit-wide Phi3/Phi9 zero statement on both members of the spectral pair. -/
theorem z180_k18_forced_order_three_nine_zeros_both_sides
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    (∀ d : ZMod 180, frequencyOrder 180 d = 3 → CyclotomicZero 180 A d) ∧
      (∀ d : ZMod 180, frequencyOrder 180 d = 9 → CyclotomicZero 180 A d) ∧
      (∀ d : ZMod 180, frequencyOrder 180 d = 3 → CyclotomicZero 180 L d) ∧
      (∀ d : ZMod 180, frequencyOrder 180 d = 9 → CyclotomicZero 180 L d) := by
  have hforced := z180_k18_forced_transform_zeros_of_spectral hSpec hcard
  exact ⟨
    z180_k18_zero_at_order_three_of_transform_zero hforced.1,
    z180_k18_zero_at_order_nine_of_transform_zero hforced.2.1,
    z180_k18_zero_at_order_three_of_transform_zero hforced.2.2.1,
    z180_k18_zero_at_order_nine_of_transform_zero hforced.2.2.2⟩

/-- Canonical-frequency form: `60` has order three and `20` has order nine. -/
theorem z180_k18_forced_phi3_phi9_both_sides
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    CyclotomicZero 180 A 60 ∧
      CyclotomicZero 180 A 20 ∧
      CyclotomicZero 180 L 60 ∧
      CyclotomicZero 180 L 20 := by
  have hzeros := z180_k18_forced_order_three_nine_zeros_both_sides hSpec hcard
  exact ⟨
    hzeros.1 60 (by decide),
    hzeros.2.1 20 (by decide),
    hzeros.2.2.1 60 (by decide),
    hzeros.2.2.2 20 (by decide)⟩

#print axioms z180_k18_forced_transform_zeros_of_spectral
#print axioms z180_k18_forced_order_three_nine_zeros_both_sides
#print axioms z180_k18_forced_phi3_phi9_both_sides

end Fuglede
