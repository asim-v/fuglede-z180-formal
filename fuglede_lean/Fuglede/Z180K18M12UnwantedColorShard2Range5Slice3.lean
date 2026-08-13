import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z168

/-!
Proof-only five-value aggregator 3 of range 5 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        165 ≤ z.val ∧ z.val < 170 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h166 : z.val < 166
  · have hzVal : z.val = 165 := (Nat.le_antisymm (Nat.le_of_lt_succ h166) hzSlice.1)
    have hzEq : z = (165 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 165 := hzVal
        _ = ((165 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (165 : ZMod 180) hd hz
    have hval : ((165 : ZMod 180).val) = 165 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h167 : z.val < 167
  · have hzVal : z.val = 166 := (Nat.le_antisymm (Nat.le_of_lt_succ h167) (Nat.le_of_not_gt h166))
    have hzEq : z = (166 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 166 := hzVal
        _ = ((166 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (166 : ZMod 180) hd hz
    have hval : ((166 : ZMod 180).val) = 166 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h168 : z.val < 168
  · have hzVal : z.val = 167 := (Nat.le_antisymm (Nat.le_of_lt_succ h168) (Nat.le_of_not_gt h167))
    have hzEq : z = (167 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 167 := hzVal
        _ = ((167 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (167 : ZMod 180) hd hz
    have hval : ((167 : ZMod 180).val) = 167 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h169 : z.val < 169
  · have hzVal : z.val = 168 := (Nat.le_antisymm (Nat.le_of_lt_succ h169) (Nat.le_of_not_gt h168))
    have hzEq : z = (168 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 168 := hzVal
        _ = ((168 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_168
      d hd w hz hw hzw hne
  have hzVal : z.val = 169 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h169))
  have hzEq : z = (169 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 169 := hzVal
      _ = ((169 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (169 : ZMod 180) hd hz
  have hval : ((169 : ZMod 180).val) = 169 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_3

end Fuglede
