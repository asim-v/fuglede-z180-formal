import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z96
import Fuglede.Z180K18M12UnwantedColorShard1Z98

/-!
Proof-only five-value aggregator 1 of range 3 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        95 ≤ z.val ∧ z.val < 100 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h96 : z.val < 96
  · have hzVal : z.val = 95 := (Nat.le_antisymm (Nat.le_of_lt_succ h96) hzSlice.1)
    have hzEq : z = (95 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 95 := hzVal
        _ = ((95 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (95 : ZMod 180) hd hz
    have hval : ((95 : ZMod 180).val) = 95 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h97 : z.val < 97
  · have hzVal : z.val = 96 := (Nat.le_antisymm (Nat.le_of_lt_succ h97) (Nat.le_of_not_gt h96))
    have hzEq : z = (96 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 96 := hzVal
        _ = ((96 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_96
      d hd w hz hw hzw hne
  by_cases h98 : z.val < 98
  · have hzVal : z.val = 97 := (Nat.le_antisymm (Nat.le_of_lt_succ h98) (Nat.le_of_not_gt h97))
    have hzEq : z = (97 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 97 := hzVal
        _ = ((97 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (97 : ZMod 180) hd hz
    have hval : ((97 : ZMod 180).val) = 97 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h99 : z.val < 99
  · have hzVal : z.val = 98 := (Nat.le_antisymm (Nat.le_of_lt_succ h99) (Nat.le_of_not_gt h98))
    have hzEq : z = (98 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 98 := hzVal
        _ = ((98 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_98
      d hd w hz hw hzw hne
  have hzVal : z.val = 99 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h99))
  have hzEq : z = (99 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 99 := hzVal
      _ = ((99 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (99 : ZMod 180) hd hz
  have hval : ((99 : ZMod 180).val) = 99 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_1

end Fuglede
