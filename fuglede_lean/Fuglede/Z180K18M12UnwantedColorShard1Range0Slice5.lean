import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z26

/-!
Proof-only five-value aggregator 5 of range 0 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        25 ≤ z.val ∧ z.val < 30 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h26 : z.val < 26
  · have hzVal : z.val = 25 := (Nat.le_antisymm (Nat.le_of_lt_succ h26) hzSlice.1)
    have hzEq : z = (25 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 25 := hzVal
        _ = ((25 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (25 : ZMod 180) hd hz
    have hval : ((25 : ZMod 180).val) = 25 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h27 : z.val < 27
  · have hzVal : z.val = 26 := (Nat.le_antisymm (Nat.le_of_lt_succ h27) (Nat.le_of_not_gt h26))
    have hzEq : z = (26 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 26 := hzVal
        _ = ((26 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_26
      d hd w hz hw hzw hne
  by_cases h28 : z.val < 28
  · have hzVal : z.val = 27 := (Nat.le_antisymm (Nat.le_of_lt_succ h28) (Nat.le_of_not_gt h27))
    have hzEq : z = (27 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 27 := hzVal
        _ = ((27 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (27 : ZMod 180) hd hz
    have hval : ((27 : ZMod 180).val) = 27 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h29 : z.val < 29
  · have hzVal : z.val = 28 := (Nat.le_antisymm (Nat.le_of_lt_succ h29) (Nat.le_of_not_gt h28))
    have hzEq : z = (28 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 28 := hzVal
        _ = ((28 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (28 : ZMod 180) hd hz
    have hval : ((28 : ZMod 180).val) = 28 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 29 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h29))
  have hzEq : z = (29 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 29 := hzVal
      _ = ((29 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (29 : ZMod 180) hd hz
  have hval : ((29 : ZMod 180).val) = 29 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_5

end Fuglede
