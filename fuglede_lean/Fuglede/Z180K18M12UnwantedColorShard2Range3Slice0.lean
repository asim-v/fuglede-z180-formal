import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z90
import Fuglede.Z180K18M12UnwantedColorShard2Z93

/-!
Proof-only five-value aggregator 0 of range 3 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_3_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        90 ≤ z.val ∧ z.val < 95 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h91 : z.val < 91
  · have hzVal : z.val = 90 := (Nat.le_antisymm (Nat.le_of_lt_succ h91) hzSlice.1)
    have hzEq : z = (90 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 90 := hzVal
        _ = ((90 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_90
      d hd w hz hw hzw hne
  by_cases h92 : z.val < 92
  · have hzVal : z.val = 91 := (Nat.le_antisymm (Nat.le_of_lt_succ h92) (Nat.le_of_not_gt h91))
    have hzEq : z = (91 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 91 := hzVal
        _ = ((91 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (91 : ZMod 180) hd hz
    have hval : ((91 : ZMod 180).val) = 91 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h93 : z.val < 93
  · have hzVal : z.val = 92 := (Nat.le_antisymm (Nat.le_of_lt_succ h93) (Nat.le_of_not_gt h92))
    have hzEq : z = (92 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 92 := hzVal
        _ = ((92 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (92 : ZMod 180) hd hz
    have hval : ((92 : ZMod 180).val) = 92 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h94 : z.val < 94
  · have hzVal : z.val = 93 := (Nat.le_antisymm (Nat.le_of_lt_succ h94) (Nat.le_of_not_gt h93))
    have hzEq : z = (93 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 93 := hzVal
        _ = ((93 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_93
      d hd w hz hw hzw hne
  have hzVal : z.val = 94 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h94))
  have hzEq : z = (94 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 94 := hzVal
      _ = ((94 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (94 : ZMod 180) hd hz
  have hval : ((94 : ZMod 180).val) = 94 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_3_slice_0

end Fuglede
