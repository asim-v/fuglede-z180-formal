import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z3

/-!
Proof-only five-value aggregator 0 of range 0 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        z.val < 5 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h1 : z.val < 1
  · have hzVal : z.val = 0 := (Nat.le_antisymm (Nat.le_of_lt_succ h1) (Nat.zero_le z.val))
    have hzEq : z = (0 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 0 := hzVal
        _ = ((0 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (0 : ZMod 180) hd hz
    have hval : ((0 : ZMod 180).val) = 0 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h2 : z.val < 2
  · have hzVal : z.val = 1 := (Nat.le_antisymm (Nat.le_of_lt_succ h2) (Nat.le_of_not_gt h1))
    have hzEq : z = (1 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 1 := hzVal
        _ = ((1 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (1 : ZMod 180) hd hz
    have hval : ((1 : ZMod 180).val) = 1 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h3 : z.val < 3
  · have hzVal : z.val = 2 := (Nat.le_antisymm (Nat.le_of_lt_succ h3) (Nat.le_of_not_gt h2))
    have hzEq : z = (2 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 2 := hzVal
        _ = ((2 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (2 : ZMod 180) hd hz
    have hval : ((2 : ZMod 180).val) = 2 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h4 : z.val < 4
  · have hzVal : z.val = 3 := (Nat.le_antisymm (Nat.le_of_lt_succ h4) (Nat.le_of_not_gt h3))
    have hzEq : z = (3 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 3 := hzVal
        _ = ((3 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_3
      d hd w hz hw hzw hne
  have hzVal : z.val = 4 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice) (Nat.le_of_not_gt h4))
  have hzEq : z = (4 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 4 := hzVal
      _ = ((4 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (4 : ZMod 180) hd hz
  have hval : ((4 : ZMod 180).val) = 4 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_0_slice_0

end Fuglede
