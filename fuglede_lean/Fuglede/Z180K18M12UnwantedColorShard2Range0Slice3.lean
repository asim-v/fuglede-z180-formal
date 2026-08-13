import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z18

/-!
Proof-only five-value aggregator 3 of range 0 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        15 ≤ z.val ∧ z.val < 20 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h16 : z.val < 16
  · have hzVal : z.val = 15 := (Nat.le_antisymm (Nat.le_of_lt_succ h16) hzSlice.1)
    have hzEq : z = (15 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 15 := hzVal
        _ = ((15 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (15 : ZMod 180) hd hz
    have hval : ((15 : ZMod 180).val) = 15 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h17 : z.val < 17
  · have hzVal : z.val = 16 := (Nat.le_antisymm (Nat.le_of_lt_succ h17) (Nat.le_of_not_gt h16))
    have hzEq : z = (16 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 16 := hzVal
        _ = ((16 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (16 : ZMod 180) hd hz
    have hval : ((16 : ZMod 180).val) = 16 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h18 : z.val < 18
  · have hzVal : z.val = 17 := (Nat.le_antisymm (Nat.le_of_lt_succ h18) (Nat.le_of_not_gt h17))
    have hzEq : z = (17 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 17 := hzVal
        _ = ((17 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (17 : ZMod 180) hd hz
    have hval : ((17 : ZMod 180).val) = 17 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h19 : z.val < 19
  · have hzVal : z.val = 18 := (Nat.le_antisymm (Nat.le_of_lt_succ h19) (Nat.le_of_not_gt h18))
    have hzEq : z = (18 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 18 := hzVal
        _ = ((18 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_18
      d hd w hz hw hzw hne
  have hzVal : z.val = 19 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h19))
  have hzEq : z = (19 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 19 := hzVal
      _ = ((19 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (19 : ZMod 180) hd hz
  have hval : ((19 : ZMod 180).val) = 19 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_3

end Fuglede
