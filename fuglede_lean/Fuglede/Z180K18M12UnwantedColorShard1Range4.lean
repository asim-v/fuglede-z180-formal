import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice0
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice1
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice2
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice3
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice4
import Fuglede.Z180K18M12UnwantedColorShard1Range4Slice5

/-!
Proof-only width-thirty range aggregator 4 for unwanted-order index 1.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_4 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        120 ≤ z.val ∧ z.val < 150 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h125 : z.val < 125
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_0
      d hd z w ⟨hzRange.1, h125⟩ hz hw hzw hne
  by_cases h130 : z.val < 130
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_1
      d hd z w ⟨Nat.le_of_not_gt h125, h130⟩ hz hw hzw hne
  by_cases h135 : z.val < 135
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_2
      d hd z w ⟨Nat.le_of_not_gt h130, h135⟩ hz hw hzw hne
  by_cases h140 : z.val < 140
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_3
      d hd z w ⟨Nat.le_of_not_gt h135, h140⟩ hz hw hzw hne
  by_cases h145 : z.val < 145
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_4
      d hd z w ⟨Nat.le_of_not_gt h140, h145⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_1_range_4_slice_5
    d hd z w ⟨Nat.le_of_not_gt h145, hzRange.2⟩ hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_4

end Fuglede

