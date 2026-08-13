import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z60
import Fuglede.Z180K18M12UnwantedColorShard1Z62

/-!
Proof-only five-value aggregator 0 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        60 ≤ z.val ∧ z.val < 65 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h61 : z.val < 61
  · have hzVal : z.val = 60 := (Nat.le_antisymm (Nat.le_of_lt_succ h61) hzSlice.1)
    have hzEq : z = (60 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 60 := hzVal
        _ = ((60 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_60
      d hd w hz hw hzw hne
  by_cases h62 : z.val < 62
  · have hzVal : z.val = 61 := (Nat.le_antisymm (Nat.le_of_lt_succ h62) (Nat.le_of_not_gt h61))
    have hzEq : z = (61 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 61 := hzVal
        _ = ((61 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (61 : ZMod 180) hd hz
    have hval : ((61 : ZMod 180).val) = 61 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h63 : z.val < 63
  · have hzVal : z.val = 62 := (Nat.le_antisymm (Nat.le_of_lt_succ h63) (Nat.le_of_not_gt h62))
    have hzEq : z = (62 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 62 := hzVal
        _ = ((62 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_62
      d hd w hz hw hzw hne
  by_cases h64 : z.val < 64
  · have hzVal : z.val = 63 := (Nat.le_antisymm (Nat.le_of_lt_succ h64) (Nat.le_of_not_gt h63))
    have hzEq : z = (63 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 63 := hzVal
        _ = ((63 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (63 : ZMod 180) hd hz
    have hval : ((63 : ZMod 180).val) = 63 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 64 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h64))
  have hzEq : z = (64 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 64 := hzVal
      _ = ((64 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (64 : ZMod 180) hd hz
  have hval : ((64 : ZMod 180).val) = 64 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_0

end Fuglede
