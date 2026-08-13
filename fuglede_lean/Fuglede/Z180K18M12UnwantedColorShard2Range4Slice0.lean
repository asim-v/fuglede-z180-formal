import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z120
import Fuglede.Z180K18M12UnwantedColorShard2Z123

/-!
Proof-only five-value aggregator 0 of range 4 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        120 ≤ z.val ∧ z.val < 125 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h121 : z.val < 121
  · have hzVal : z.val = 120 := (Nat.le_antisymm (Nat.le_of_lt_succ h121) hzSlice.1)
    have hzEq : z = (120 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 120 := hzVal
        _ = ((120 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_120
      d hd w hz hw hzw hne
  by_cases h122 : z.val < 122
  · have hzVal : z.val = 121 := (Nat.le_antisymm (Nat.le_of_lt_succ h122) (Nat.le_of_not_gt h121))
    have hzEq : z = (121 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 121 := hzVal
        _ = ((121 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (121 : ZMod 180) hd hz
    have hval : ((121 : ZMod 180).val) = 121 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h123 : z.val < 123
  · have hzVal : z.val = 122 := (Nat.le_antisymm (Nat.le_of_lt_succ h123) (Nat.le_of_not_gt h122))
    have hzEq : z = (122 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 122 := hzVal
        _ = ((122 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (122 : ZMod 180) hd hz
    have hval : ((122 : ZMod 180).val) = 122 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h124 : z.val < 124
  · have hzVal : z.val = 123 := (Nat.le_antisymm (Nat.le_of_lt_succ h124) (Nat.le_of_not_gt h123))
    have hzEq : z = (123 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 123 := hzVal
        _ = ((123 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_123
      d hd w hz hw hzw hne
  have hzVal : z.val = 124 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h124))
  have hzEq : z = (124 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 124 := hzVal
      _ = ((124 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (124 : ZMod 180) hd hz
  have hval : ((124 : ZMod 180).val) = 124 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_0

end Fuglede
