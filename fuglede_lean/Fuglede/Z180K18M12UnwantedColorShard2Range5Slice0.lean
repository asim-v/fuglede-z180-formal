import Fuglede.Z180K18M12UnwantedCommonPossibleShard2

/-!
Proof-only five-value aggregator 0 of range 5 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        150 ≤ z.val ∧ z.val < 155 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h151 : z.val < 151
  · have hzVal : z.val = 150 := (Nat.le_antisymm (Nat.le_of_lt_succ h151) hzSlice.1)
    have hzEq : z = (150 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 150 := hzVal
        _ = ((150 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (150 : ZMod 180) hd hz
    have hval : ((150 : ZMod 180).val) = 150 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h152 : z.val < 152
  · have hzVal : z.val = 151 := (Nat.le_antisymm (Nat.le_of_lt_succ h152) (Nat.le_of_not_gt h151))
    have hzEq : z = (151 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 151 := hzVal
        _ = ((151 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (151 : ZMod 180) hd hz
    have hval : ((151 : ZMod 180).val) = 151 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h153 : z.val < 153
  · have hzVal : z.val = 152 := (Nat.le_antisymm (Nat.le_of_lt_succ h153) (Nat.le_of_not_gt h152))
    have hzEq : z = (152 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 152 := hzVal
        _ = ((152 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (152 : ZMod 180) hd hz
    have hval : ((152 : ZMod 180).val) = 152 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h154 : z.val < 154
  · have hzVal : z.val = 153 := (Nat.le_antisymm (Nat.le_of_lt_succ h154) (Nat.le_of_not_gt h153))
    have hzEq : z = (153 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 153 := hzVal
        _ = ((153 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (153 : ZMod 180) hd hz
    have hval : ((153 : ZMod 180).val) = 153 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 154 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h154))
  have hzEq : z = (154 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 154 := hzVal
      _ = ((154 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (154 : ZMod 180) hd hz
  have hval : ((154 : ZMod 180).val) = 154 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_0

end Fuglede
