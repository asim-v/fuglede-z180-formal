import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z138

/-!
Proof-only five-value aggregator 3 of range 4 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        135 ≤ z.val ∧ z.val < 140 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h136 : z.val < 136
  · have hzVal : z.val = 135 := (Nat.le_antisymm (Nat.le_of_lt_succ h136) hzSlice.1)
    have hzEq : z = (135 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 135 := hzVal
        _ = ((135 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (135 : ZMod 180) hd hz
    have hval : ((135 : ZMod 180).val) = 135 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h137 : z.val < 137
  · have hzVal : z.val = 136 := (Nat.le_antisymm (Nat.le_of_lt_succ h137) (Nat.le_of_not_gt h136))
    have hzEq : z = (136 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 136 := hzVal
        _ = ((136 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (136 : ZMod 180) hd hz
    have hval : ((136 : ZMod 180).val) = 136 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h138 : z.val < 138
  · have hzVal : z.val = 137 := (Nat.le_antisymm (Nat.le_of_lt_succ h138) (Nat.le_of_not_gt h137))
    have hzEq : z = (137 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 137 := hzVal
        _ = ((137 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (137 : ZMod 180) hd hz
    have hval : ((137 : ZMod 180).val) = 137 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h139 : z.val < 139
  · have hzVal : z.val = 138 := (Nat.le_antisymm (Nat.le_of_lt_succ h139) (Nat.le_of_not_gt h138))
    have hzEq : z = (138 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 138 := hzVal
        _ = ((138 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_138
      d hd w hz hw hzw hne
  have hzVal : z.val = 139 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h139))
  have hzEq : z = (139 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 139 := hzVal
      _ = ((139 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (139 : ZMod 180) hd hz
  have hval : ((139 : ZMod 180).val) = 139 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_3

end Fuglede
