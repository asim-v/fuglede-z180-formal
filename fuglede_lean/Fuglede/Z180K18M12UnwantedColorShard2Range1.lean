import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice0
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice1
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice2
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice3
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice4
import Fuglede.Z180K18M12UnwantedColorShard2Range1Slice5

/-!
Proof-only width-thirty range aggregator 1 for unwanted-order index 2.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        30 ≤ z.val ∧ z.val < 60 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h35 : z.val < 35
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_0
      d hd z w ⟨hzRange.1, h35⟩ hz hw hzw hne
  by_cases h40 : z.val < 40
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_1
      d hd z w ⟨Nat.le_of_not_gt h35, h40⟩ hz hw hzw hne
  by_cases h45 : z.val < 45
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_2
      d hd z w ⟨Nat.le_of_not_gt h40, h45⟩ hz hw hzw hne
  by_cases h50 : z.val < 50
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_3
      d hd z w ⟨Nat.le_of_not_gt h45, h50⟩ hz hw hzw hne
  by_cases h55 : z.val < 55
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_4
      d hd z w ⟨Nat.le_of_not_gt h50, h55⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_2_range_1_slice_5
    d hd z w ⟨Nat.le_of_not_gt h55, hzRange.2⟩ hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_1

end Fuglede

