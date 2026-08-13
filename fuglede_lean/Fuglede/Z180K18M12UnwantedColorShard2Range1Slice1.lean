import Fuglede.Z180K18M12UnwantedCommonPossibleShard2
import Fuglede.Z180K18M12UnwantedColorShard2Z39

/-!
Proof-only five-value aggregator 1 of range 1 for
unwanted-order index 2.  It dispatches each concrete first vertex
to a literal finite leaf, or closes a mechanically classified vacuous case.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        35 ≤ z.val ∧ z.val < 40 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzSlice hz hw hzw hne
  by_cases h36 : z.val < 36
  · have hzVal : z.val = 35 := (Nat.le_antisymm (Nat.le_of_lt_succ h36) hzSlice.1)
    have hzEq : z = (35 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 35 := hzVal
        _ = ((35 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (35 : ZMod 180) hd hz
    have hval : ((35 : ZMod 180).val) = 35 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h37 : z.val < 37
  · have hzVal : z.val = 36 := (Nat.le_antisymm (Nat.le_of_lt_succ h37) (Nat.le_of_not_gt h36))
    have hzEq : z = (36 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 36 := hzVal
        _ = ((36 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (36 : ZMod 180) hd hz
    have hval : ((36 : ZMod 180).val) = 36 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h38 : z.val < 38
  · have hzVal : z.val = 37 := (Nat.le_antisymm (Nat.le_of_lt_succ h38) (Nat.le_of_not_gt h37))
    have hzEq : z = (37 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 37 := hzVal
        _ = ((37 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (37 : ZMod 180) hd hz
    have hval : ((37 : ZMod 180).val) = 37 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  by_cases h39 : z.val < 39
  · have hzVal : z.val = 38 := (Nat.le_antisymm (Nat.le_of_lt_succ h39) (Nat.le_of_not_gt h38))
    have hzEq : z = (38 : ZMod 180) := by
      apply ZMod.val_injective
      calc
        z.val = 38 := hzVal
        _ = ((38 : ZMod 180).val) := by
          decide
    subst z
    have hpossible :=
      z180_k18_m12_unwantedCommonNeighbor_val_mem_shard_2
        d (38 : ZMod 180) hd hz
    have hval : ((38 : ZMod 180).val) = 38 := by
      decide
    simp only [hval] at hpossible
    norm_num [z180K18M12UnwantedCommonPossibleValues2] at hpossible
  have hzVal : z.val = 39 := (Nat.le_antisymm (Nat.le_of_lt_succ hzSlice.2) (Nat.le_of_not_gt h39))
  have hzEq : z = (39 : ZMod 180) := by
    apply ZMod.val_injective
    calc
      z.val = 39 := hzVal
      _ = ((39 : ZMod 180).val) := by
        decide
  subst z
  exact z180_k18_m12_unwantedColor_separates_shard_2_z_39
    d hd w hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_1

end Fuglede
