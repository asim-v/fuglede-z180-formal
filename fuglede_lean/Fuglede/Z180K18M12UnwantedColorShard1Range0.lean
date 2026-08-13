import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice0
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice1
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice2
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice3
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice4
import Fuglede.Z180K18M12UnwantedColorShard1Range0Slice5

/-!
Proof-only width-thirty range aggregator 0 for unwanted-order index 1.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_range_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        z.val < 30 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h5 : z.val < 5
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_0
      d hd z w h5 hz hw hzw hne
  by_cases h10 : z.val < 10
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_1
      d hd z w ⟨Nat.le_of_not_gt h5, h10⟩ hz hw hzw hne
  by_cases h15 : z.val < 15
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_2
      d hd z w ⟨Nat.le_of_not_gt h10, h15⟩ hz hw hzw hne
  by_cases h20 : z.val < 20
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_3
      d hd z w ⟨Nat.le_of_not_gt h15, h20⟩ hz hw hzw hne
  by_cases h25 : z.val < 25
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_4
      d hd z w ⟨Nat.le_of_not_gt h20, h25⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_1_range_0_slice_5
    d hd z w ⟨Nat.le_of_not_gt h25, hzRange⟩ hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_range_0

end Fuglede

