import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z57

/-!
Proof-only five-value aggregator 5 of range 1 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        55 ≤ z.val ∧ z.val < 60 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h56 : z.val < 56
  · have hzVal : z.val = 55 := (Nat.le_antisymm (Nat.le_of_lt_succ h56) hzSlice.1)
    have hzEq : z = (55 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 55 := hzVal
        _ = ((55 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (55 : ZMod 180) hd hz
    have hval : ((55 : ZMod 180).val) = 55 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h57 : z.val < 57
  · have hzVal : z.val = 56 := (Nat.le_antisymm (Nat.le_of_lt_succ h57) (Nat.le_of_not_gt h56))
    have hzEq : z = (56 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 56 := hzVal
        _ = ((56 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (56 : ZMod 180) hd hz
    have hval : ((56 : ZMod 180).val) = 56 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h58 : z.val < 58
  · have hzVal : z.val = 57 := (Nat.le_antisymm (Nat.le_of_lt_succ h58) (Nat.le_of_not_gt h57))
    have hzEq : z = (57 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 57 := hzVal
        _ = ((57 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_57
      d hd w hz hw hzw hne
  by_cases h59 : z.val < 59
  · have hzVal : z.val = 58 := (Nat.le_antisymm (Nat.le_of_lt_succ h59) (Nat.le_of_not_gt h58))
    have hzEq : z = (58 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 58 := hzVal
        _ = ((58 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (58 : ZMod 180) hd hz
    have hval : ((58 : ZMod 180).val) = 58 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 59 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h59))
  have hzEq : z = (59 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 59 := hzVal
      _ = ((59 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (59 : ZMod 180) hd hz
  have hval : ((59 : ZMod 180).val) = 59 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_5

end Fuglede
