import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z86
import Fuglede.Z180K18M12UnwantedColorShard1Z87

/-!
Proof-only five-value aggregator 5 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        85 ≤ z.val ∧ z.val < 90 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h86 : z.val < 86
  · have hzVal : z.val = 85 := (Nat.le_antisymm (Nat.le_of_lt_succ h86) hzSlice.1)
    have hzEq : z = (85 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 85 := hzVal
        _ = ((85 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (85 : ZMod 180) hd hz
    have hval : ((85 : ZMod 180).val) = 85 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h87 : z.val < 87
  · have hzVal : z.val = 86 := (Nat.le_antisymm (Nat.le_of_lt_succ h87) (Nat.le_of_not_gt h86))
    have hzEq : z = (86 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 86 := hzVal
        _ = ((86 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_86
      d hd w hz hw hzw hne
  by_cases h88 : z.val < 88
  · have hzVal : z.val = 87 := (Nat.le_antisymm (Nat.le_of_lt_succ h88) (Nat.le_of_not_gt h87))
    have hzEq : z = (87 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 87 := hzVal
        _ = ((87 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_87
      d hd w hz hw hzw hne
  by_cases h89 : z.val < 89
  · have hzVal : z.val = 88 := (Nat.le_antisymm (Nat.le_of_lt_succ h89) (Nat.le_of_not_gt h88))
    have hzEq : z = (88 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 88 := hzVal
        _ = ((88 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (88 : ZMod 180) hd hz
    have hval : ((88 : ZMod 180).val) = 88 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 89 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h89))
  have hzEq : z = (89 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 89 := hzVal
      _ = ((89 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (89 : ZMod 180) hd hz
  have hval : ((89 : ZMod 180).val) = 89 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_5

end Fuglede
