import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU3

namespace Fuglede

theorem z36_card_le_five_branchU3 (L : Finset (ZMod 36))
    (h2 : ¬ Z36HasDifferenceOrder L 2)
    (h4 : ¬ Z36HasDifferenceOrder L 4)
    (h9 : ¬ Z36HasDifferenceOrder L 9)
    (h18 : ¬ Z36HasDifferenceOrder L 18)
    (h36 : ¬ Z36HasDifferenceOrder L 36) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U3 := z36_pair_order_mem_of_flags (L := L) (U := U3)
    (Or.inr h2) (Or.inl (by decide)) (Or.inr h4) (Or.inl (by decide))
    (Or.inr h9) (Or.inl (by decide)) (Or.inr h18) (Or.inr h36)
  have hc := z36_card_le_of_global_coloring L U3 colorU3 z36_colorU3_separation ha
  omega

#print axioms z36_card_le_five_branchU3
end Fuglede
