import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU1

namespace Fuglede

theorem z36_card_le_five_branchU1 (L : Finset (ZMod 36))
    (h2 : ¬ Z36HasDifferenceOrder L 2)
    (h3 : ¬ Z36HasDifferenceOrder L 3)
    (h4 : ¬ Z36HasDifferenceOrder L 4)
    (h6 : ¬ Z36HasDifferenceOrder L 6)
    (h12 : ¬ Z36HasDifferenceOrder L 12) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U1 := z36_pair_order_mem_of_flags (L := L) (U := U1)
    (Or.inr h2) (Or.inr h3) (Or.inr h4) (Or.inr h6)
    (Or.inl (by decide)) (Or.inr h12) (Or.inl (by decide)) (Or.inl (by decide))
  have hc := z36_card_le_of_global_coloring L U1 colorU1 z36_colorU1_separation ha
  omega

#print axioms z36_card_le_five_branchU1
end Fuglede
