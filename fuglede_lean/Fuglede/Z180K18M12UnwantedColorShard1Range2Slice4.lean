import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z82
import Fuglede.Z180K18M12UnwantedColorShard1Z84

/-!
Proof-only five-value aggregator 4 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        80 ≤ z.val ∧ z.val < 85 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h81 : z.val < 81
  · have hzVal : z.val = 80 := (Nat.le_antisymm (Nat.le_of_lt_succ h81) hzSlice.1)
    have hzEq : z = (80 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 80 := hzVal
        _ = ((80 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (80 : ZMod 180) hd hz
    have hval : ((80 : ZMod 180).val) = 80 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h82 : z.val < 82
  · have hzVal : z.val = 81 := (Nat.le_antisymm (Nat.le_of_lt_succ h82) (Nat.le_of_not_gt h81))
    have hzEq : z = (81 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 81 := hzVal
        _ = ((81 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (81 : ZMod 180) hd hz
    have hval : ((81 : ZMod 180).val) = 81 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h83 : z.val < 83
  · have hzVal : z.val = 82 := (Nat.le_antisymm (Nat.le_of_lt_succ h83) (Nat.le_of_not_gt h82))
    have hzEq : z = (82 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 82 := hzVal
        _ = ((82 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_82
      d hd w hz hw hzw hne
  by_cases h84 : z.val < 84
  · have hzVal : z.val = 83 := (Nat.le_antisymm (Nat.le_of_lt_succ h84) (Nat.le_of_not_gt h83))
    have hzEq : z = (83 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 83 := hzVal
        _ = ((83 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (83 : ZMod 180) hd hz
    have hval : ((83 : ZMod 180).val) = 83 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 84 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h84))
  have hzEq : z = (84 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 84 := hzVal
      _ = ((84 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_84
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_4

end Fuglede
