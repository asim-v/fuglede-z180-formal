import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU8

namespace Fuglede

theorem z36_card_le_five_branchU8 (L : Finset (ZMod 36))
    (h4 : ¬ Z36HasDifferenceOrder L 4)
    (h6 : ¬ Z36HasDifferenceOrder L 6)
    (h9 : ¬ Z36HasDifferenceOrder L 9)
    (h18 : ¬ Z36HasDifferenceOrder L 18)
    (h36 : ¬ Z36HasDifferenceOrder L 36) : L.card ≤ 5 := by
  by_cases hEmpty : L = ∅
  · simp [hEmpty]
  have hL : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U8 := z36_pair_order_mem_of_flags (L := L) (U := U8)
    (Or.inl (by decide)) (Or.inl (by decide)) (Or.inr h4) (Or.inr h6)
    (Or.inr h9) (Or.inl (by decide)) (Or.inr h18) (Or.inr h36)
  exact z36_card_le_five_of_neighbor_coloring L U8 colorU8Neighbor
    z36_colorU8_neighbor_separation ha hL

#print axioms z36_card_le_five_branchU8
end Fuglede
