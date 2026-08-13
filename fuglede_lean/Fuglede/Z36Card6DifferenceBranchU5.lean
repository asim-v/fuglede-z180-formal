import Fuglede.Z36Card6DifferenceStructuralCore
import Fuglede.Z36Card6DifferenceColorU5

namespace Fuglede

theorem z36_card_le_five_branchU5 (L : Finset (ZMod 36))
    (h3 : ¬ Z36HasDifferenceOrder L 3)
    (h4 : ¬ Z36HasDifferenceOrder L 4)
    (h12 : ¬ Z36HasDifferenceOrder L 12)
    (h18 : ¬ Z36HasDifferenceOrder L 18) : L.card ≤ 5 := by
  by_cases hEmpty : L = ∅
  · simp [hEmpty]
  have hL : L.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have ha : ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
      frequencyOrder 36 (x - y) ∈ U5 := z36_pair_order_mem_of_flags (L := L) (U := U5)
    (Or.inl (by decide)) (Or.inr h3) (Or.inr h4) (Or.inl (by decide))
    (Or.inl (by decide)) (Or.inr h12) (Or.inr h18) (Or.inl (by decide))
  exact z36_card_le_five_of_neighbor_coloring L U5 colorU5Neighbor
    z36_colorU5_neighbor_separation ha hL

#print axioms z36_card_le_five_branchU5
end Fuglede
