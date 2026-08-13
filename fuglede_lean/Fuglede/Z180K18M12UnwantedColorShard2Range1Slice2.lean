import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z42

/-!
Proof-only five-value aggregator 2 of range 1 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        40 ≤ z.val ∧ z.val < 45 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h41 : z.val < 41
  · have hzVal : z.val = 40 := (Nat.le_antisymm (Nat.le_of_lt_succ h41) hzSlice.1)
    have hzEq : z = (40 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 40 := hzVal
        _ = ((40 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (40 : ZMod 180) hd hz
    have hval : ((40 : ZMod 180).val) = 40 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h42 : z.val < 42
  · have hzVal : z.val = 41 := (Nat.le_antisymm (Nat.le_of_lt_succ h42) (Nat.le_of_not_gt h41))
    have hzEq : z = (41 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 41 := hzVal
        _ = ((41 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (41 : ZMod 180) hd hz
    have hval : ((41 : ZMod 180).val) = 41 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h43 : z.val < 43
  · have hzVal : z.val = 42 := (Nat.le_antisymm (Nat.le_of_lt_succ h43) (Nat.le_of_not_gt h42))
    have hzEq : z = (42 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 42 := hzVal
        _ = ((42 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_42
      d hd w hz hw hzw hne
  by_cases h44 : z.val < 44
  · have hzVal : z.val = 43 := (Nat.le_antisymm (Nat.le_of_lt_succ h44) (Nat.le_of_not_gt h43))
    have hzEq : z = (43 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 43 := hzVal
        _ = ((43 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (43 : ZMod 180) hd hz
    have hval : ((43 : ZMod 180).val) = 43 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 44 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h44))
  have hzEq : z = (44 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 44 := hzVal
      _ = ((44 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (44 : ZMod 180) hd hz
  have hval : ((44 : ZMod 180).val) = 44 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_2

end Fuglede
