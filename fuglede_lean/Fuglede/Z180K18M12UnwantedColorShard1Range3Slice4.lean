import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z111
import Fuglede.Z180K18M12UnwantedColorShard1Z114

/-!
Proof-only five-value aggregator 4 of range 3 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        110 ≤ z.val ∧ z.val < 115 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h111 : z.val < 111
  · have hzVal : z.val = 110 := (Nat.le_antisymm (Nat.le_of_lt_succ h111) hzSlice.1)
    have hzEq : z = (110 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 110 := hzVal
        _ = ((110 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (110 : ZMod 180) hd hz
    have hval : ((110 : ZMod 180).val) = 110 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h112 : z.val < 112
  · have hzVal : z.val = 111 := (Nat.le_antisymm (Nat.le_of_lt_succ h112) (Nat.le_of_not_gt h111))
    have hzEq : z = (111 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 111 := hzVal
        _ = ((111 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_111
      d hd w hz hw hzw hne
  by_cases h113 : z.val < 113
  · have hzVal : z.val = 112 := (Nat.le_antisymm (Nat.le_of_lt_succ h113) (Nat.le_of_not_gt h112))
    have hzEq : z = (112 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 112 := hzVal
        _ = ((112 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (112 : ZMod 180) hd hz
    have hval : ((112 : ZMod 180).val) = 112 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h114 : z.val < 114
  · have hzVal : z.val = 113 := (Nat.le_antisymm (Nat.le_of_lt_succ h114) (Nat.le_of_not_gt h113))
    have hzEq : z = (113 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 113 := hzVal
        _ = ((113 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (113 : ZMod 180) hd hz
    have hval : ((113 : ZMod 180).val) = 113 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  have hzVal : z.val = 114 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h114))
  have hzEq : z = (114 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 114 := hzVal
      _ = ((114 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_1_z_114
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_4

end Fuglede
