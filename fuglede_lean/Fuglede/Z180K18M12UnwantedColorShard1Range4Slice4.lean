import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z141
import Fuglede.Z180K18M12UnwantedColorShard1Z142

/-!
Proof-only five-value aggregator 4 of range 4 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        140 ≤ z.val ∧ z.val < 145 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h141 : z.val < 141
  · have hzVal : z.val = 140 := (Nat.le_antisymm (Nat.le_of_lt_succ h141) hzSlice.1)
    have hzEq : z = (140 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 140 := hzVal
        _ = ((140 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (140 : ZMod 180) hd hz
    have hval : ((140 : ZMod 180).val) = 140 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h142 : z.val < 142
  · have hzVal : z.val = 141 := (Nat.le_antisymm (Nat.le_of_lt_succ h142) (Nat.le_of_not_gt h141))
    have hzEq : z = (141 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 141 := hzVal
        _ = ((141 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_141
      d hd w hz hw hzw hne
  by_cases h143 : z.val < 143
  · have hzVal : z.val = 142 := (Nat.le_antisymm (Nat.le_of_lt_succ h143) (Nat.le_of_not_gt h142))
    have hzEq : z = (142 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 142 := hzVal
        _ = ((142 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_142
      d hd w hz hw hzw hne
  by_cases h144 : z.val < 144
  · have hzVal : z.val = 143 := (Nat.le_antisymm (Nat.le_of_lt_succ h144) (Nat.le_of_not_gt h143))
    have hzEq : z = (143 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 143 := hzVal
        _ = ((143 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (143 : ZMod 180) hd hz
    have hval : ((143 : ZMod 180).val) = 143 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 144 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h144))
  have hzEq : z = (144 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 144 := hzVal
      _ = ((144 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (144 : ZMod 180) hd hz
  have hval : ((144 : ZMod 180).val) = 144 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_4

end Fuglede
