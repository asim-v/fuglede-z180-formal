import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z156
import Fuglede.Z180K18M12UnwantedColorShard2Z159

/-!
Proof-only five-value aggregator 1 of range 5 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        155 ≤ z.val ∧ z.val < 160 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h156 : z.val < 156
  · have hzVal : z.val = 155 := (Nat.le_antisymm (Nat.le_of_lt_succ h156) hzSlice.1)
    have hzEq : z = (155 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 155 := hzVal
        _ = ((155 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (155 : ZMod 180) hd hz
    have hval : ((155 : ZMod 180).val) = 155 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h157 : z.val < 157
  · have hzVal : z.val = 156 := (Nat.le_antisymm (Nat.le_of_lt_succ h157) (Nat.le_of_not_gt h156))
    have hzEq : z = (156 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 156 := hzVal
        _ = ((156 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_156
      d hd w hz hw hzw hne
  by_cases h158 : z.val < 158
  · have hzVal : z.val = 157 := (Nat.le_antisymm (Nat.le_of_lt_succ h158) (Nat.le_of_not_gt h157))
    have hzEq : z = (157 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 157 := hzVal
        _ = ((157 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (157 : ZMod 180) hd hz
    have hval : ((157 : ZMod 180).val) = 157 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h159 : z.val < 159
  · have hzVal : z.val = 158 := (Nat.le_antisymm (Nat.le_of_lt_succ h159) (Nat.le_of_not_gt h158))
    have hzEq : z = (158 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 158 := hzVal
        _ = ((158 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (158 : ZMod 180) hd hz
    have hval : ((158 : ZMod 180).val) = 158 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 159 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h159))
  have hzEq : z = (159 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 159 := hzVal
      _ = ((159 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_2_z_159
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_1

end Fuglede
