import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU2

namespace Fuglede

theorem z36_card_le_five_branchU2 (L : Finset (ZMod 36))
    (h2 : ¬ Z36HasDifferenceOrder L 2)
    (h3 : ¬ Z36HasDifferenceOrder L 3)
    (h6 : ¬ Z36HasDifferenceOrder L 6)
    (h36 : ¬ Z36HasDifferenceOrder L 36) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U2 := z36_pair_order_mem_of_flags (L := L) (U := U2)
    (Or.inr h2) (Or.inr h3) (Or.inl (by decide)) (Or.inr h6)
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr h36)
  have hc := z36_card_le_of_global_coloring L U2 colorU2 z36_colorU2_separation ha
  omega

#print axioms z36_card_le_five_branchU2
end Fuglede
