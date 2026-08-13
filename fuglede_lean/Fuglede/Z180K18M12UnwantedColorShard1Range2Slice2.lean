import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z74

/-!
Proof-only five-value aggregator 2 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        70 ≤ z.val ∧ z.val < 75 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h71 : z.val < 71
  · have hzVal : z.val = 70 := (Nat.le_antisymm (Nat.le_of_lt_succ h71) hzSlice.1)
    have hzEq : z = (70 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 70 := hzVal
        _ = ((70 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (70 : ZMod 180) hd hz
    have hval : ((70 : ZMod 180).val) = 70 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h72 : z.val < 72
  · have hzVal : z.val = 71 := (Nat.le_antisymm (Nat.le_of_lt_succ h72) (Nat.le_of_not_gt h71))
    have hzEq : z = (71 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 71 := hzVal
        _ = ((71 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (71 : ZMod 180) hd hz
    have hval : ((71 : ZMod 180).val) = 71 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h73 : z.val < 73
  · have hzVal : z.val = 72 := (Nat.le_antisymm (Nat.le_of_lt_succ h73) (Nat.le_of_not_gt h72))
    have hzEq : z = (72 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 72 := hzVal
        _ = ((72 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (72 : ZMod 180) hd hz
    have hval : ((72 : ZMod 180).val) = 72 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h74 : z.val < 74
  · have hzVal : z.val = 73 := (Nat.le_antisymm (Nat.le_of_lt_succ h74) (Nat.le_of_not_gt h73))
    have hzEq : z = (73 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 73 := hzVal
        _ = ((73 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (73 : ZMod 180) hd hz
    have hval : ((73 : ZMod 180).val) = 73 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 74 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h74))
  have hzEq : z = (74 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 74 := hzVal
      _ = ((74 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_74
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_2

end Fuglede
