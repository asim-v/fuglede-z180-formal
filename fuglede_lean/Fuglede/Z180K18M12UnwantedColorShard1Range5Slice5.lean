import Fuglede.Z180K18M12UnwantedCommonPossibleShard1
import Fuglede.Z180K18M12UnwantedColorShard1Z177
import Fuglede.Z180K18M12UnwantedColorShard1Z178

/-!
Proof-only five-value aggregator 5 of range 5 for
unwanted-order index 1.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_5_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        175 ≤ z.val →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h176 : z.val < 176
  · have hzVal : z.val = 175 := (Nat.le_antisymm (Nat.le_of_lt_succ h176) hzSlice)
    have hzEq : z = (175 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 175 := hzVal
        _ = ((175 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (175 : ZMod 180) hd hz
    have hval : ((175 : ZMod 180).val) = 175 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h177 : z.val < 177
  · have hzVal : z.val = 176 := (Nat.le_antisymm (Nat.le_of_lt_succ h177) (Nat.le_of_not_gt h176))
    have hzEq : z = (176 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 176 := hzVal
        _ = ((176 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
        d (176 : ZMod 180) hd hz
    have hval : ((176 : ZMod 180).val) = 176 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible
  by_cases h178 : z.val < 178
  · have hzVal : z.val = 177 := (Nat.le_antisymm (Nat.le_of_lt_succ h178) (Nat.le_of_not_gt h177))
    have hzEq : z = (177 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 177 := hzVal
        _ = ((177 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_177
      d hd w hz hw hzw hne
  by_cases h179 : z.val < 179
  · have hzVal : z.val = 178 := (Nat.le_antisymm (Nat.le_of_lt_succ h179) (Nat.le_of_not_gt h178))
    have hzEq : z = (178 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 178 := hzVal
        _ = ((178 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_1_z_178
      d hd w hz hw hzw hne
  have hzVal : z.val = 179 := (Nat.le_antisymm (Nat.le_of_lt_succ z.val_lt) (Nat.le_of_not_gt h179))
  have hzEq : z = (179 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 179 := hzVal
      _ = ((179 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_1
      d (179 : ZMod 180) hd hz
  have hval : ((179 : ZMod 180).val) = 179 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues1] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_5_slice_5

end Fuglede
