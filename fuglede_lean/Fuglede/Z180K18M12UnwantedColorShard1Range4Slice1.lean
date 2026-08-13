import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z126
import Fuglede.Z180K18M12UnwantedColorShard1Z129

/-!
Proof-only five-value aggregator 1 of range 4 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        125 ≤ z.val ∧ z.val < 130 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h126 : z.val < 126
  · have hzVal : z.val = 125 := (Nat.le_antisymm (Nat.le_of_lt_succ h126) hzSlice.1)
    have hzEq : z = (125 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 125 := hzVal
        _ = ((125 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (125 : ZMod 180) hd hz
    have hval : ((125 : ZMod 180).val) = 125 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h127 : z.val < 127
  · have hzVal : z.val = 126 := (Nat.le_antisymm (Nat.le_of_lt_succ h127) (Nat.le_of_not_gt h126))
    have hzEq : z = (126 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 126 := hzVal
        _ = ((126 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_126
      d hd w hz hw hzw hne
  by_cases h128 : z.val < 128
  · have hzVal : z.val = 127 := (Nat.le_antisymm (Nat.le_of_lt_succ h128) (Nat.le_of_not_gt h127))
    have hzEq : z = (127 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 127 := hzVal
        _ = ((127 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (127 : ZMod 180) hd hz
    have hval : ((127 : ZMod 180).val) = 127 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h129 : z.val < 129
  · have hzVal : z.val = 128 := (Nat.le_antisymm (Nat.le_of_lt_succ h129) (Nat.le_of_not_gt h128))
    have hzEq : z = (128 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 128 := hzVal
        _ = ((128 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (128 : ZMod 180) hd hz
    have hval : ((128 : ZMod 180).val) = 128 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 129 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h129))
  have hzEq : z = (129 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 129 := hzVal
      _ = ((129 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_129
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_1

end Fuglede
