import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z6

/-!
Proof-only five-value aggregator 1 of range 0 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        5 ≤ z.val ∧ z.val < 10 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h6 : z.val < 6
  · have hzVal : z.val = 5 := (Nat.le_antisymm (Nat.le_of_lt_succ h6) hzSlice.1)
    have hzEq : z = (5 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 5 := hzVal
        _ = ((5 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (5 : ZMod 180) hd hz
    have hval : ((5 : ZMod 180).val) = 5 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h7 : z.val < 7
  · have hzVal : z.val = 6 := (Nat.le_antisymm (Nat.le_of_lt_succ h7) (Nat.le_of_not_gt h6))
    have hzEq : z = (6 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 6 := hzVal
        _ = ((6 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_6
      d hd w hz hw hzw hne
  by_cases h8 : z.val < 8
  · have hzVal : z.val = 7 := (Nat.le_antisymm (Nat.le_of_lt_succ h8) (Nat.le_of_not_gt h7))
    have hzEq : z = (7 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 7 := hzVal
        _ = ((7 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (7 : ZMod 180) hd hz
    have hval : ((7 : ZMod 180).val) = 7 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h9 : z.val < 9
  · have hzVal : z.val = 8 := (Nat.le_antisymm (Nat.le_of_lt_succ h9) (Nat.le_of_not_gt h8))
    have hzEq : z = (8 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 8 := hzVal
        _ = ((8 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (8 : ZMod 180) hd hz
    have hval : ((8 : ZMod 180).val) = 8 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 9 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h9))
  have hzEq : z = (9 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 9 := hzVal
      _ = ((9 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (9 : ZMod 180) hd hz
  have hval : ((9 : ZMod 180).val) = 9 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_1

end Fuglede
