import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z78

/-!
Proof-only five-value aggregator 3 of range 2 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        75 ≤ z.val ∧ z.val < 80 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h76 : z.val < 76
  · have hzVal : z.val = 75 := (Nat.le_antisymm (Nat.le_of_lt_succ h76) hzSlice.1)
    have hzEq : z = (75 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 75 := hzVal
        _ = ((75 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (75 : ZMod 180) hd hz
    have hval : ((75 : ZMod 180).val) = 75 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h77 : z.val < 77
  · have hzVal : z.val = 76 := (Nat.le_antisymm (Nat.le_of_lt_succ h77) (Nat.le_of_not_gt h76))
    have hzEq : z = (76 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 76 := hzVal
        _ = ((76 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (76 : ZMod 180) hd hz
    have hval : ((76 : ZMod 180).val) = 76 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h78 : z.val < 78
  · have hzVal : z.val = 77 := (Nat.le_antisymm (Nat.le_of_lt_succ h78) (Nat.le_of_not_gt h77))
    have hzEq : z = (77 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 77 := hzVal
        _ = ((77 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (77 : ZMod 180) hd hz
    have hval : ((77 : ZMod 180).val) = 77 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h79 : z.val < 79
  · have hzVal : z.val = 78 := (Nat.le_antisymm (Nat.le_of_lt_succ h79) (Nat.le_of_not_gt h78))
    have hzEq : z = (78 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 78 := hzVal
        _ = ((78 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_78
      d hd w hz hw hzw hne
  have hzVal : z.val = 79 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h79))
  have hzEq : z = (79 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 79 := hzVal
      _ = ((79 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (79 : ZMod 180) hd hz
  have hval : ((79 : ZMod 180).val) = 79 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_2_slice_3

end Fuglede
