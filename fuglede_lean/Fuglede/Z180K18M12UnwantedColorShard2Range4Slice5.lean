import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z147

/-!
Proof-only five-value aggregator 5 of range 4 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        145 ≤ z.val ∧ z.val < 150 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h146 : z.val < 146
  · have hzVal : z.val = 145 := (Nat.le_antisymm (Nat.le_of_lt_succ h146) hzSlice.1)
    have hzEq : z = (145 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 145 := hzVal
        _ = ((145 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (145 : ZMod 180) hd hz
    have hval : ((145 : ZMod 180).val) = 145 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h147 : z.val < 147
  · have hzVal : z.val = 146 := (Nat.le_antisymm (Nat.le_of_lt_succ h147) (Nat.le_of_not_gt h146))
    have hzEq : z = (146 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 146 := hzVal
        _ = ((146 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (146 : ZMod 180) hd hz
    have hval : ((146 : ZMod 180).val) = 146 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h148 : z.val < 148
  · have hzVal : z.val = 147 := (Nat.le_antisymm (Nat.le_of_lt_succ h148) (Nat.le_of_not_gt h147))
    have hzEq : z = (147 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 147 := hzVal
        _ = ((147 : ZMod 180).val) := by
          decide
    subst z
    exact z180_k18_m12_unwantedColor_separates_shard_2_z_147
      d hd w hz hw hzw hne
  by_cases h149 : z.val < 149
  · have hzVal : z.val = 148 := (Nat.le_antisymm (Nat.le_of_lt_succ h149) (Nat.le_of_not_gt h148))
    have hzEq : z = (148 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 148 := hzVal
        _ = ((148 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (148 : ZMod 180) hd hz
    have hval : ((148 : ZMod 180).val) = 148 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 149 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h149))
  have hzEq : z = (149 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 149 := hzVal
      _ = ((149 : ZMod 180).val) := by
        decide
  subst z
  have hpossible :=
    z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
      d (149 : ZMod 180) hd hz
  have hval : ((149 : ZMod 180).val) = 149 := by
    decide
  simp only [hval] at hpossible
  norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_4_slice_5

end Fuglede
