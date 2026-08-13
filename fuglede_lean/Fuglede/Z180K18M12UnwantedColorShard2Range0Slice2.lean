import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z12

/-!
Proof-only five-value aggregator 2 of range 0 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        10 ≤ z.val ∧ z.val < 15 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
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
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (10 : ZMod 180) hd hz
    have hval : ((10 : ZMod 180).val) = 10 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
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
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (11 : ZMod 180) hd hz
    have hval : ((11 : ZMod 180).val) = 11 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h13 : z.val < 13
  · have hzVal : z.val = 12 := (Nat.le_antisymm (Nat.le_of_lt_succ h13) (Nat.le_of_not_gt h12))
    have hzEq : z = (12 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 12 := hzVal
        _ = ((12 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_12
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
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (13 : ZMod 180) hd hz
    have hval : ((13 : ZMod 180).val) = 13 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 14 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h14))
  have hzEq : z = (14 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 14 := hzVal
      _ = ((14 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (14 : ZMod 180) hd hz
  have hval : ((14 : ZMod 180).val) = 14 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_2

end Fuglede
