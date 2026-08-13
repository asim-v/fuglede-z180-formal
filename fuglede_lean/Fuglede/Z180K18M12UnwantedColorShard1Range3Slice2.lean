import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z102

/-!
Proof-only five-value aggregator 2 of range 3 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        100 ≤ z.val ∧ z.val < 105 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h101 : z.val < 101
  · have hzVal : z.val = 100 := (Nat.le_antisymm (Nat.le_of_lt_succ h101) hzSlice.1)
    have hzEq : z = (100 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 100 := hzVal
        _ = ((100 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (100 : ZMod 180) hd hz
    have hval : ((100 : ZMod 180).val) = 100 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h102 : z.val < 102
  · have hzVal : z.val = 101 := (Nat.le_antisymm (Nat.le_of_lt_succ h102) (Nat.le_of_not_gt h101))
    have hzEq : z = (101 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 101 := hzVal
        _ = ((101 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (101 : ZMod 180) hd hz
    have hval : ((101 : ZMod 180).val) = 101 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h103 : z.val < 103
  · have hzVal : z.val = 102 := (Nat.le_antisymm (Nat.le_of_lt_succ h103) (Nat.le_of_not_gt h102))
    have hzEq : z = (102 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 102 := hzVal
        _ = ((102 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_102
      d hd w hz hw hzw hne
  by_cases h104 : z.val < 104
  · have hzVal : z.val = 103 := (Nat.le_antisymm (Nat.le_of_lt_succ h104) (Nat.le_of_not_gt h103))
    have hzEq : z = (103 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 103 := hzVal
        _ = ((103 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (103 : ZMod 180) hd hz
    have hval : ((103 : ZMod 180).val) = 103 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 104 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h104))
  have hzEq : z = (104 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 104 := hzVal
      _ = ((104 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (104 : ZMod 180) hd hz
  have hval : ((104 : ZMod 180).val) = 104 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_2

end Fuglede
