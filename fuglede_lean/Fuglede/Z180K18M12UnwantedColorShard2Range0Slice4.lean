import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z21
import Fuglede.Z180K18M12UnwantedColorShard2Z24

/-!
Proof-only five-value aggregator 4 of range 0 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        20 ≤ z.val ∧ z.val < 25 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h21 : z.val < 21
  · have hzVal : z.val = 20 := (Nat.le_antisymm (Nat.le_of_lt_succ h21) hzSlice.1)
    have hzEq : z = (20 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 20 := hzVal
        _ = ((20 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (20 : ZMod 180) hd hz
    have hval : ((20 : ZMod 180).val) = 20 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h22 : z.val < 22
  · have hzVal : z.val = 21 := (Nat.le_antisymm (Nat.le_of_lt_succ h22) (Nat.le_of_not_gt h21))
    have hzEq : z = (21 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 21 := hzVal
        _ = ((21 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_21
      d hd w hz hw hzw hne
  by_cases h23 : z.val < 23
  · have hzVal : z.val = 22 := (Nat.le_antisymm (Nat.le_of_lt_succ h23) (Nat.le_of_not_gt h22))
    have hzEq : z = (22 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 22 := hzVal
        _ = ((22 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (22 : ZMod 180) hd hz
    have hval : ((22 : ZMod 180).val) = 22 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h24 : z.val < 24
  · have hzVal : z.val = 23 := (Nat.le_antisymm (Nat.le_of_lt_succ h24) (Nat.le_of_not_gt h23))
    have hzEq : z = (23 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 23 := hzVal
        _ = ((23 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (23 : ZMod 180) hd hz
    have hval : ((23 : ZMod 180).val) = 23 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 24 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h24))
  have hzEq : z = (24 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 24 := hzVal
      _ = ((24 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_2_z_24
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_4

end Fuglede
