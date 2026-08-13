import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice0
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice1
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice2
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice3
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice4
import Fuglede.Z180K18M12UnwantedColorShard1Range3Slice5

/-!
Proof-only width-thirty range aggregator 3 for unwanted-order index 1.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_3 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        90 ≤ z.val ∧ z.val < 120 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h95 : z.val < 95
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_0
      d hd z w ⟨hzRange.1, h95⟩ hz hw hzw hne
  by_cases h100 : z.val < 100
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_1
      d hd z w ⟨Nat.le_of_not_gt h95, h100⟩ hz hw hzw hne
  by_cases h105 : z.val < 105
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_2
      d hd z w ⟨Nat.le_of_not_gt h100, h105⟩ hz hw hzw hne
  by_cases h110 : z.val < 110
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_3
      d hd z w ⟨Nat.le_of_not_gt h105, h110⟩ hz hw hzw hne
  by_cases h115 : z.val < 115
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_4
      d hd z w ⟨Nat.le_of_not_gt h110, h115⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_1_range_3_slice_5
    d hd z w ⟨Nat.le_of_not_gt h115, hzRange.2⟩ hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_3

end Fuglede

