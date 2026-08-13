import Fuglede.Z180K18M12UnwantedCommonPossibleShard2

/-!
Proof-only five-value aggregator 5 of range 3 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_3_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        115 ≤ z.val ∧ z.val < 120 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h116 : z.val < 116
  · have hzVal : z.val = 115 := (Nat.le_antisymm (Nat.le_of_lt_succ h116) hzSlice.1)
    have hzEq : z = (115 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 115 := hzVal
        _ = ((115 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (115 : ZMod 180) hd hz
    have hval : ((115 : ZMod 180).val) = 115 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h117 : z.val < 117
  · have hzVal : z.val = 116 := (Nat.le_antisymm (Nat.le_of_lt_succ h117) (Nat.le_of_not_gt h116))
    have hzEq : z = (116 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 116 := hzVal
        _ = ((116 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (116 : ZMod 180) hd hz
    have hval : ((116 : ZMod 180).val) = 116 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h118 : z.val < 118
  · have hzVal : z.val = 117 := (Nat.le_antisymm (Nat.le_of_lt_succ h118) (Nat.le_of_not_gt h117))
    have hzEq : z = (117 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 117 := hzVal
        _ = ((117 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (117 : ZMod 180) hd hz
    have hval : ((117 : ZMod 180).val) = 117 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h119 : z.val < 119
  · have hzVal : z.val = 118 := (Nat.le_antisymm (Nat.le_of_lt_succ h119) (Nat.le_of_not_gt h118))
    have hzEq : z = (118 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 118 := hzVal
        _ = ((118 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (118 : ZMod 180) hd hz
    have hval : ((118 : ZMod 180).val) = 118 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 119 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h119))
  have hzEq : z = (119 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 119 := hzVal
      _ = ((119 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (119 : ZMod 180) hd hz
  have hval : ((119 : ZMod 180).val) = 119 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_3_slice_5

end Fuglede
