import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z51
import Fuglede.Z180K18M12UnwantedColorShard2Z54

/-!
Proof-only five-value aggregator 4 of range 1 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        50 ≤ z.val ∧ z.val < 55 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h51 : z.val < 51
  · have hzVal : z.val = 50 := (Nat.le_antisymm (Nat.le_of_lt_succ h51) hzSlice.1)
    have hzEq : z = (50 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 50 := hzVal
        _ = ((50 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (50 : ZMod 180) hd hz
    have hval : ((50 : ZMod 180).val) = 50 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h52 : z.val < 52
  · have hzVal : z.val = 51 := (Nat.le_antisymm (Nat.le_of_lt_succ h52) (Nat.le_of_not_gt h51))
    have hzEq : z = (51 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 51 := hzVal
        _ = ((51 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_51
      d hd w hz hw hzw hne
  by_cases h53 : z.val < 53
  · have hzVal : z.val = 52 := (Nat.le_antisymm (Nat.le_of_lt_succ h53) (Nat.le_of_not_gt h52))
    have hzEq : z = (52 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 52 := hzVal
        _ = ((52 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (52 : ZMod 180) hd hz
    have hval : ((52 : ZMod 180).val) = 52 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h54 : z.val < 54
  · have hzVal : z.val = 53 := (Nat.le_antisymm (Nat.le_of_lt_succ h54) (Nat.le_of_not_gt h53))
    have hzEq : z = (53 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 53 := hzVal
        _ = ((53 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (53 : ZMod 180) hd hz
    have hval : ((53 : ZMod 180).val) = 53 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 54 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h54))
  have hzEq : z = (54 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 54 := hzVal
      _ = ((54 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_2_z_54
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_4

end Fuglede
