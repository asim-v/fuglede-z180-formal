import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z48

/-!
Proof-only five-value aggregator 3 of range 1 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        45 ≤ z.val ∧ z.val < 50 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h46 : z.val < 46
  · have hzVal : z.val = 45 := (Nat.le_antisymm (Nat.le_of_lt_succ h46) hzSlice.1)
    have hzEq : z = (45 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 45 := hzVal
        _ = ((45 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (45 : ZMod 180) hd hz
    have hval : ((45 : ZMod 180).val) = 45 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h47 : z.val < 47
  · have hzVal : z.val = 46 := (Nat.le_antisymm (Nat.le_of_lt_succ h47) (Nat.le_of_not_gt h46))
    have hzEq : z = (46 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 46 := hzVal
        _ = ((46 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (46 : ZMod 180) hd hz
    have hval : ((46 : ZMod 180).val) = 46 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h48 : z.val < 48
  · have hzVal : z.val = 47 := (Nat.le_antisymm (Nat.le_of_lt_succ h48) (Nat.le_of_not_gt h47))
    have hzEq : z = (47 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 47 := hzVal
        _ = ((47 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (47 : ZMod 180) hd hz
    have hval : ((47 : ZMod 180).val) = 47 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h49 : z.val < 49
  · have hzVal : z.val = 48 := (Nat.le_antisymm (Nat.le_of_lt_succ h49) (Nat.le_of_not_gt h48))
    have hzEq : z = (48 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 48 := hzVal
        _ = ((48 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_48
      d hd w hz hw hzw hne
  have hzVal : z.val = 49 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h49))
  have hzEq : z = (49 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 49 := hzVal
      _ = ((49 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (49 : ZMod 180) hd hz
  have hval : ((49 : ZMod 180).val) = 49 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_3

end Fuglede
