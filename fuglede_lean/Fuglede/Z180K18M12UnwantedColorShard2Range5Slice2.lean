import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z162

/-!
Proof-only five-value aggregator 2 of range 5 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        160 ≤ z.val ∧ z.val < 165 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h161 : z.val < 161
  · have hzVal : z.val = 160 := (Nat.le_antisymm (Nat.le_of_lt_succ h161) hzSlice.1)
    have hzEq : z = (160 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 160 := hzVal
        _ = ((160 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (160 : ZMod 180) hd hz
    have hval : ((160 : ZMod 180).val) = 160 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h162 : z.val < 162
  · have hzVal : z.val = 161 := (Nat.le_antisymm (Nat.le_of_lt_succ h162) (Nat.le_of_not_gt h161))
    have hzEq : z = (161 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 161 := hzVal
        _ = ((161 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (161 : ZMod 180) hd hz
    have hval : ((161 : ZMod 180).val) = 161 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h163 : z.val < 163
  · have hzVal : z.val = 162 := (Nat.le_antisymm (Nat.le_of_lt_succ h163) (Nat.le_of_not_gt h162))
    have hzEq : z = (162 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 162 := hzVal
        _ = ((162 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_162
      d hd w hz hw hzw hne
  by_cases h164 : z.val < 164
  · have hzVal : z.val = 163 := (Nat.le_antisymm (Nat.le_of_lt_succ h164) (Nat.le_of_not_gt h163))
    have hzEq : z = (163 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 163 := hzVal
        _ = ((163 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (163 : ZMod 180) hd hz
    have hval : ((163 : ZMod 180).val) = 163 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 164 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h164))
  have hzEq : z = (164 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 164 := hzVal
      _ = ((164 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (164 : ZMod 180) hd hz
  have hval : ((164 : ZMod 180).val) = 164 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_2

end Fuglede
