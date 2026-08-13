import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z12
import Fuglede.Z180K18M12UnwantedColorShard1Z14

/-!
Proof-only five-value aggregator 2 of range 0 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        10 ≤ z.val ∧ z.val < 15 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h11 : z.val < 11
  · have hzVal : z.val = 10 := (Nat.le_antisymm (Nat.le_of_lt_succ h11) hzSlice.1)
    have hzEq : z = (10 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 10 := hzVal
        _ = ((10 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (10 : ZMod 180) hd hz
    have hval : ((10 : ZMod 180).val) = 10 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h12 : z.val < 12
  · have hzVal : z.val = 11 := (Nat.le_antisymm (Nat.le_of_lt_succ h12) (Nat.le_of_not_gt h11))
    have hzEq : z = (11 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 11 := hzVal
        _ = ((11 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (11 : ZMod 180) hd hz
    have hval : ((11 : ZMod 180).val) = 11 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h13 : z.val < 13
  · have hzVal : z.val = 12 := (Nat.le_antisymm (Nat.le_of_lt_succ h13) (Nat.le_of_not_gt h12))
    have hzEq : z = (12 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 12 := hzVal
        _ = ((12 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_12
      d hd w hz hw hzw hne
  by_cases h14 : z.val < 14
  · have hzVal : z.val = 13 := (Nat.le_antisymm (Nat.le_of_lt_succ h14) (Nat.le_of_not_gt h13))
    have hzEq : z = (13 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 13 := hzVal
        _ = ((13 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (13 : ZMod 180) hd hz
    have hval : ((13 : ZMod 180).val) = 13 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 14 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h14))
  have hzEq : z = (14 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 14 := hzVal
      _ = ((14 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_14
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_2

end Fuglede
