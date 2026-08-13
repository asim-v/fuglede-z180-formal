import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z174

/-!
Proof-only five-value aggregator 4 of range 5 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        170 ≤ z.val ∧ z.val < 175 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h171 : z.val < 171
  · have hzVal : z.val = 170 := (Nat.le_antisymm (Nat.le_of_lt_succ h171) hzSlice.1)
    have hzEq : z = (170 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 170 := hzVal
        _ = ((170 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (170 : ZMod 180) hd hz
    have hval : ((170 : ZMod 180).val) = 170 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h172 : z.val < 172
  · have hzVal : z.val = 171 := (Nat.le_antisymm (Nat.le_of_lt_succ h172) (Nat.le_of_not_gt h171))
    have hzEq : z = (171 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 171 := hzVal
        _ = ((171 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (171 : ZMod 180) hd hz
    have hval : ((171 : ZMod 180).val) = 171 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h173 : z.val < 173
  · have hzVal : z.val = 172 := (Nat.le_antisymm (Nat.le_of_lt_succ h173) (Nat.le_of_not_gt h172))
    have hzEq : z = (172 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 172 := hzVal
        _ = ((172 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (172 : ZMod 180) hd hz
    have hval : ((172 : ZMod 180).val) = 172 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h174 : z.val < 174
  · have hzVal : z.val = 173 := (Nat.le_antisymm (Nat.le_of_lt_succ h174) (Nat.le_of_not_gt h173))
    have hzEq : z = (173 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 173 := hzVal
        _ = ((173 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (173 : ZMod 180) hd hz
    have hval : ((173 : ZMod 180).val) = 173 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 174 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h174))
  have hzEq : z = (174 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 174 := hzVal
      _ = ((174 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_2_z_174
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_4

end Fuglede
