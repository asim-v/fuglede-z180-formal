import Fuglede.Z36Card6DifferenceBranchU1
import Fuglede.Z36Card6DifferenceBranchU2
import Fuglede.Z36Card6DifferenceBranchU3
import Fuglede.Z36Card6DifferenceBranchU4
import Fuglede.Z36Card6DifferenceBranchU5
import Fuglede.Z36Card6DifferenceBranchU6
import Fuglede.Z36Card6DifferenceBranchU7
import Fuglede.Z36Card6DifferenceBranchU8
import Fuglede.Z36Card6DifferenceBranchU9
import Mathlib.Tactic

/-! Tiny dispatcher for the nine independently checked structural branches. -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem z36_nine_pattern_negation_cover
    (L : Finset (ZMod 36))
    (h : ¬ Z36Card6NineDifferencePatterns L) :
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 3) ∧
      (¬ Z36HasDifferenceOrder L 4) ∧ (¬ Z36HasDifferenceOrder L 6) ∧
      (¬ Z36HasDifferenceOrder L 12)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 3) ∧
      (¬ Z36HasDifferenceOrder L 6) ∧ (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 4) ∧
      (¬ Z36HasDifferenceOrder L 9) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 2) ∧ (¬ Z36HasDifferenceOrder L 9) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 4) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 9)) ∨
    ((¬ Z36HasDifferenceOrder L 3) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 4) ∧ (¬ Z36HasDifferenceOrder L 6) ∧
      (¬ Z36HasDifferenceOrder L 9) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) ∨
    ((¬ Z36HasDifferenceOrder L 6) ∧ (¬ Z36HasDifferenceOrder L 9) ∧
      (¬ Z36HasDifferenceOrder L 12) ∧ (¬ Z36HasDifferenceOrder L 18) ∧
      (¬ Z36HasDifferenceOrder L 36)) := by
  unfold Z36Card6NineDifferencePatterns at h
  have hnPat1 : ¬ (Z36HasDifferenceOrder L 2 ∧ Z36HasDifferenceOrder L 3 ∧
      Z36HasDifferenceOrder L 6) := by
    intro hp
    exact h (Or.inl hp)
  have hnPat2 : ¬ (Z36HasDifferenceOrder L 2 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 18) := by
    intro hp
    exact h (Or.inr (Or.inl hp))
  have hnPat3 : ¬ (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 4 ∧
      Z36HasDifferenceOrder L 12) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inl hp)))
  have hnPat4 : ¬ (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 9) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inl hp))))
  have hnPat5 : ¬ (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 18) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
  have hnPat6 : ¬ (Z36HasDifferenceOrder L 3 ∧ Z36HasDifferenceOrder L 36) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))))
  have hnPat7 : ¬ (Z36HasDifferenceOrder L 4 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 36) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))))
  have hnPat8 : ¬ (Z36HasDifferenceOrder L 6 ∧ Z36HasDifferenceOrder L 9 ∧
      Z36HasDifferenceOrder L 18) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl hp))))))))
  have hnPat9 : ¬ (Z36HasDifferenceOrder L 9 ∧ Z36HasDifferenceOrder L 12 ∧
      Z36HasDifferenceOrder L 36) := by
    intro hp
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr hp))))))))
  by_cases h3 : Z36HasDifferenceOrder L 3
  · have hn9 : ¬ Z36HasDifferenceOrder L 9 := fun h9 => hnPat4 ⟨h3, h9⟩
    have hn18 : ¬ Z36HasDifferenceOrder L 18 := fun h18 => hnPat5 ⟨h3, h18⟩
    have hn36 : ¬ Z36HasDifferenceOrder L 36 := fun h36 => hnPat6 ⟨h3, h36⟩
    by_cases h2 : Z36HasDifferenceOrder L 2
    · have hn6 : ¬ Z36HasDifferenceOrder L 6 := fun h6 => hnPat1 ⟨h2, h3, h6⟩
      by_cases h4 : Z36HasDifferenceOrder L 4
      · have hn12 : ¬ Z36HasDifferenceOrder L 12 :=
          fun h12 => hnPat3 ⟨h3, h4, h12⟩
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr ⟨hn6, hn9, hn12, hn18, hn36⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inl ⟨h4, hn6, hn9, hn18, hn36⟩
    · by_cases h4 : Z36HasDifferenceOrder L 4
      · have hn12 : ¬ Z36HasDifferenceOrder L 12 :=
          fun h12 => hnPat3 ⟨h3, h4, h12⟩
        exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h2, hn9, hn12, hn18, hn36⟩
      · exact Or.inr <| Or.inr <| Or.inl ⟨h2, h4, hn9, hn18, hn36⟩
  · by_cases h9 : Z36HasDifferenceOrder L 9
    · by_cases h18 : Z36HasDifferenceOrder L 18
      · have hn2 : ¬ Z36HasDifferenceOrder L 2 := fun h2 => hnPat2 ⟨h2, h9, h18⟩
        have hn6 : ¬ Z36HasDifferenceOrder L 6 := fun h6 => hnPat8 ⟨h6, h9, h18⟩
        by_cases h36 : Z36HasDifferenceOrder L 36
        · have hn4 : ¬ Z36HasDifferenceOrder L 4 := fun h4 => hnPat7 ⟨h4, h9, h36⟩
          have hn12 : ¬ Z36HasDifferenceOrder L 12 :=
            fun h12 => hnPat9 ⟨h9, h12, h36⟩
          exact Or.inl ⟨hn2, h3, hn4, hn6, hn12⟩
        · exact Or.inr <| Or.inl ⟨hn2, h3, hn6, h36⟩
      · by_cases h36 : Z36HasDifferenceOrder L 36
        · have hn4 : ¬ Z36HasDifferenceOrder L 4 := fun h4 => hnPat7 ⟨h4, h9, h36⟩
          have hn12 : ¬ Z36HasDifferenceOrder L 12 :=
            fun h12 => hnPat9 ⟨h9, h12, h36⟩
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl ⟨h3, hn4, hn12, h18⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl ⟨h3, h18, h36⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl ⟨h3, h9⟩

/-- Every six-element subset of `ZMod 36` contains one of the nine minimal
difference-order patterns. -/
theorem z36_card6_nine_difference_patterns_structural_sharded
    (L : Finset (ZMod 36)) (hcard : L.card = 6) :
    Z36Card6NineDifferencePatterns L := by
  by_contra hnot
  rcases z36_nine_pattern_negation_cover L hnot with
    h | h | h | h | h | h | h | h | h
  · have hc := z36_card_le_five_branchU1 L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    omega
  · have hc := z36_card_le_five_branchU2 L h.1 h.2.1 h.2.2.1 h.2.2.2
    omega
  · have hc := z36_card_le_five_branchU3 L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    omega
  · have hc := z36_card_le_five_branchU4 L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    omega
  · have hc := z36_card_le_five_branchU5 L h.1 h.2.1 h.2.2.1 h.2.2.2
    omega
  · have hc := z36_card_le_five_branchU6 L h.1 h.2
    omega
  · have hc := z36_card_le_five_branchU7 L h.1 h.2.1 h.2.2
    omega
  · have hc := z36_card_le_five_branchU8 L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    omega
  · have hc := z36_card_le_five_branchU9 L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    omega

#print axioms z36_card6_nine_difference_patterns_structural_sharded

end Fuglede
