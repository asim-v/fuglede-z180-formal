import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z106

/-!
Proof-only five-value aggregator 3 of range 3 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        105 ≤ z.val ∧ z.val < 110 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h106 : z.val < 106
  · have hzVal : z.val = 105 := (Nat.le_antisymm (Nat.le_of_lt_succ h106) hzSlice.1)
    have hzEq : z = (105 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 105 := hzVal
        _ = ((105 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (105 : ZMod 180) hd hz
    have hval : ((105 : ZMod 180).val) = 105 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h107 : z.val < 107
  · have hzVal : z.val = 106 := (Nat.le_antisymm (Nat.le_of_lt_succ h107) (Nat.le_of_not_gt h106))
    have hzEq : z = (106 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 106 := hzVal
        _ = ((106 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_106
      d hd w hz hw hzw hne
  by_cases h108 : z.val < 108
  · have hzVal : z.val = 107 := (Nat.le_antisymm (Nat.le_of_lt_succ h108) (Nat.le_of_not_gt h107))
    have hzEq : z = (107 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 107 := hzVal
        _ = ((107 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (107 : ZMod 180) hd hz
    have hval : ((107 : ZMod 180).val) = 107 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h109 : z.val < 109
  · have hzVal : z.val = 108 := (Nat.le_antisymm (Nat.le_of_lt_succ h109) (Nat.le_of_not_gt h108))
    have hzEq : z = (108 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 108 := hzVal
        _ = ((108 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (108 : ZMod 180) hd hz
    have hval : ((108 : ZMod 180).val) = 108 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 109 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h109))
  have hzEq : z = (109 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 109 := hzVal
      _ = ((109 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (109 : ZMod 180) hd hz
  have hval : ((109 : ZMod 180).val) = 109 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_3

end Fuglede
