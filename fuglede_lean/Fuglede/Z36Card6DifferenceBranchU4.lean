import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU4

namespace Fuglede

theorem z36_card_le_five_branchU4 (L : Finset (ZMod 36))
    (h2 : ¬ Z36HasDifferenceOrder L 2)
    (h9 : ¬ Z36HasDifferenceOrder L 9)
    (h12 : ¬ Z36HasDifferenceOrder L 12)
    (h18 : ¬ Z36HasDifferenceOrder L 18)
    (h36 : ¬ Z36HasDifferenceOrder L 36) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U4 := z36_pair_order_mem_of_flags (L := L) (U := U4)
    (Or.inr h2) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inr h9) (Or.inr h12) (Or.inr h18) (Or.inr h36)
  have hc := z36_card_le_of_global_coloring L U4 colorU4 z36_colorU4_separation ha
  omega

#print axioms z36_card_le_five_branchU4
end Fuglede
