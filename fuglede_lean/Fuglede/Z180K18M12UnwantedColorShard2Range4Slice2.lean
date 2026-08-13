import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z132

/-!
Proof-only five-value aggregator 2 of range 4 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        130 ≤ z.val ∧ z.val < 135 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h131 : z.val < 131
  · have hzVal : z.val = 130 := (Nat.le_antisymm (Nat.le_of_lt_succ h131) hzSlice.1)
    have hzEq : z = (130 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 130 := hzVal
        _ = ((130 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (130 : ZMod 180) hd hz
    have hval : ((130 : ZMod 180).val) = 130 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h132 : z.val < 132
  · have hzVal : z.val = 131 := (Nat.le_antisymm (Nat.le_of_lt_succ h132) (Nat.le_of_not_gt h131))
    have hzEq : z = (131 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 131 := hzVal
        _ = ((131 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (131 : ZMod 180) hd hz
    have hval : ((131 : ZMod 180).val) = 131 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h133 : z.val < 133
  · have hzVal : z.val = 132 := (Nat.le_antisymm (Nat.le_of_lt_succ h133) (Nat.le_of_not_gt h132))
    have hzEq : z = (132 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 132 := hzVal
        _ = ((132 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_132
      d hd w hz hw hzw hne
  by_cases h134 : z.val < 134
  · have hzVal : z.val = 133 := (Nat.le_antisymm (Nat.le_of_lt_succ h134) (Nat.le_of_not_gt h133))
    have hzEq : z = (133 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 133 := hzVal
        _ = ((133 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (133 : ZMod 180) hd hz
    have hval : ((133 : ZMod 180).val) = 133 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 134 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h134))
  have hzEq : z = (134 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 134 := hzVal
      _ = ((134 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (134 : ZMod 180) hd hz
  have hval : ((134 : ZMod 180).val) = 134 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_2

end Fuglede
