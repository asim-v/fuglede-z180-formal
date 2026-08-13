import Fuglede.Z180K30OrderClosureSemantic

/-!
# Honest partial order closure for the `k = 30` branch

The exact-order relaxation currently closes only orders `9` and `36`.
This module records that boundary without asserting the six unresolved cases
or converting it into the full K30 closure certificate.
-/

namespace Fuglede

/-- The two fivefold exact-order implications that the corrected arithmetic
relaxation proves. -/
def Z180K30NineThirtySixOrderClosure (L : Finset (ZMod 180)) : Prop :=
  (0 < exactOrderDistributionInt L 9 →
      0 < exactOrderDistributionInt L 45) ∧
  (0 < exactOrderDistributionInt L 36 →
      0 < exactOrderDistributionInt L 180)

/-- Typed boundary for a future generated certificate of the two cases.
No inhabitant is asserted in this module. -/
def Z180K30JointQFLIANineThirtySixCertificate : Prop :=
  ∀ A L : Finset (ZMod 180),
    CyclotomicSpectrum 180 A L → A.card = 30 →
      Z180K30NineThirtySixOrderClosure L

/-- The partial certificate supplies fivefold order closure for an occurring
same-fifth-slice difference once its order is known to be `9` or `36`. -/
theorem z180_k30_fivefold_order_closure_of_nineThirtySix
    {L : Finset (ZMod 180)} (h : Z180K30NineThirtySixOrderClosure L)
    {y₁ y₂ : ZMod 180}
    (hy₁ : y₁ ∈ z180K30FifthSlice L (0 : ZMod 5))
    (hy₂ : y₂ ∈ z180K30FifthSlice L (0 : ZMod 5))
    (hne : y₁ ≠ y₂)
    (hc : frequencyOrder 180 (y₁ - y₂) = 9 ∨
      frequencyOrder 180 (y₁ - y₂) = 36) :
    0 < exactOrderDistributionInt L
      (frequencyOrder 180 (y₁ - y₂) * 5) := by
  have hp :=
    (z180_k30_zeroth_fifth_slice_pair_semantic_input hy₁ hy₂ hne).1
  rcases hc with h9 | h36
  · have hp9 : 0 < exactOrderDistributionInt L 9 := by
      simpa only [h9] using hp
    simpa only [h9, Nat.reduceMul] using h.1 hp9
  · have hp36 : 0 < exactOrderDistributionInt L 36 := by
      simpa only [h36] using hp
    simpa only [h36, Nat.reduceMul] using h.2 hp36

#print axioms z180_k30_fivefold_order_closure_of_nineThirtySix

end Fuglede
