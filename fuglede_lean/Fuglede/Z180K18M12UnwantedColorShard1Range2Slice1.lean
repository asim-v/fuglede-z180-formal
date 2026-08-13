import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z66
import Fuglede.Z180K18M12UnwantedColorShard1Z69

/-!
Proof-only five-value aggregator 1 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        65 ≤ z.val ∧ z.val < 70 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h66 : z.val < 66
  · have hzVal : z.val = 65 := (Nat.le_antisymm (Nat.le_of_lt_succ h66) hzSlice.1)
    have hzEq : z = (65 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 65 := hzVal
        _ = ((65 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (65 : ZMod 180) hd hz
    have hval : ((65 : ZMod 180).val) = 65 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h67 : z.val < 67
  · have hzVal : z.val = 66 := (Nat.le_antisymm (Nat.le_of_lt_succ h67) (Nat.le_of_not_gt h66))
    have hzEq : z = (66 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 66 := hzVal
        _ = ((66 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_66
      d hd w hz hw hzw hne
  by_cases h68 : z.val < 68
  · have hzVal : z.val = 67 := (Nat.le_antisymm (Nat.le_of_lt_succ h68) (Nat.le_of_not_gt h67))
    have hzEq : z = (67 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 67 := hzVal
        _ = ((67 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (67 : ZMod 180) hd hz
    have hval : ((67 : ZMod 180).val) = 67 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h69 : z.val < 69
  · have hzVal : z.val = 68 := (Nat.le_antisymm (Nat.le_of_lt_succ h69) (Nat.le_of_not_gt h68))
    have hzEq : z = (68 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 68 := hzVal
        _ = ((68 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (68 : ZMod 180) hd hz
    have hval : ((68 : ZMod 180).val) = 68 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 69 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h69))
  have hzEq : z = (69 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 69 := hzVal
      _ = ((69 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_69
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_1

end Fuglede
