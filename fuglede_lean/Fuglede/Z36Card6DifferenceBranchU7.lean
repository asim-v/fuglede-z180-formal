import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU7

namespace Fuglede

theorem z36_card_le_five_branchU7 (L : Finset (ZMod 36))
    (h3 : ¬ Z36HasDifferenceOrder L 3)
    (h18 : ¬ Z36HasDifferenceOrder L 18)
    (h36 : ¬ Z36HasDifferenceOrder L 36) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U7 := z36_pair_order_mem_of_flags (L := L) (U := U7)
    (Or.inl (by decide)) (Or.inr h3) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr h18) (Or.inr h36)
  have hc := z36_card_le_of_global_coloring L U7 colorU7 z36_colorU7_separation ha
  omega

#print axioms z36_card_le_five_branchU7
end Fuglede
