import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU6

namespace Fuglede

theorem z36_card_le_five_branchU6 (L : Finset (ZMod 36))
    (h3 : ¬ Z36HasDifferenceOrder L 3)
    (h9 : ¬ Z36HasDifferenceOrder L 9) : L.card ≤ 5 := by
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U6 := z36_pair_order_mem_of_flags (L := L) (U := U6)
    (Or.inl (by decide)) (Or.inr h3) (Or.inl (by decide)) (Or.inl (by decide))
    (Or.inr h9) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))
  have hc := z36_card_le_of_global_coloring L U6 colorU6 z36_colorU6_separation ha
  omega

#print axioms z36_card_le_five_branchU6
end Fuglede
