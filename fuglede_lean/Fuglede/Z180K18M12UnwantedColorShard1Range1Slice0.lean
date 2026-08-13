import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z33
import Fuglede.Z180K18M12UnwantedColorShard1Z34

/-!
Proof-only five-value aggregator 0 of range 1 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_1_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        30 ≤ z.val ∧ z.val < 35 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h31 : z.val < 31
  · have hzVal : z.val = 30 := (Nat.le_antisymm (Nat.le_of_lt_succ h31) hzSlice.1)
    have hzEq : z = (30 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 30 := hzVal
        _ = ((30 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (30 : ZMod 180) hd hz
    have hval : ((30 : ZMod 180).val) = 30 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h32 : z.val < 32
  · have hzVal : z.val = 31 := (Nat.le_antisymm (Nat.le_of_lt_succ h32) (Nat.le_of_not_gt h31))
    have hzEq : z = (31 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 31 := hzVal
        _ = ((31 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (31 : ZMod 180) hd hz
    have hval : ((31 : ZMod 180).val) = 31 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h33 : z.val < 33
  · have hzVal : z.val = 32 := (Nat.le_antisymm (Nat.le_of_lt_succ h33) (Nat.le_of_not_gt h32))
    have hzEq : z = (32 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 32 := hzVal
        _ = ((32 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (32 : ZMod 180) hd hz
    have hval : ((32 : ZMod 180).val) = 32 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h34 : z.val < 34
  · have hzVal : z.val = 33 := (Nat.le_antisymm (Nat.le_of_lt_succ h34) (Nat.le_of_not_gt h33))
    have hzEq : z = (33 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 33 := hzVal
        _ = ((33 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_33
      d hd w hz hw hzw hne
  have hzVal : z.val = 34 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h34))
  have hzEq : z = (34 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 34 := hzVal
      _ = ((34 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_34
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_1_slice_0

end Fuglede
