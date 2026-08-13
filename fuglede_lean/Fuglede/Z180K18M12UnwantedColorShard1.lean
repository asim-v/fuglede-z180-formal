import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard1Range0
import Fuglede.Z180K18M12UnwantedColorShard1Range1
import Fuglede.Z180K18M12UnwantedColorShard1Range2
import Fuglede.Z180K18M12UnwantedColorShard1Range3
import Fuglede.Z180K18M12UnwantedColorShard1Range4
import Fuglede.Z180K18M12UnwantedColorShard1Range5

/-!
Fixed-index aggregator for unwanted order `15`.  The six finite
checks are disjoint first-vertex ranges of width thirty; this module contains
no `decide` proof.
Payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ z w : ZMod 180,
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d z ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  intro d hd z w hz hw hzw hne
  by_cases h30 : z.val < 30
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_0
      d hd z w h30 hz hw hzw hne
  by_cases h60 : z.val < 60
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_1
      d hd z w ⟨Nat.le_of_not_gt h30, h60⟩ hz hw hzw hne
  by_cases h90 : z.val < 90
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_2
      d hd z w ⟨Nat.le_of_not_gt h60, h90⟩ hz hw hzw hne
  by_cases h120 : z.val < 120
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_3
      d hd z w ⟨Nat.le_of_not_gt h90, h120⟩ hz hw hzw hne
  by_cases h150 : z.val < 150
  · exact z180_k18_m12_unwantedColor_separates_shard_1_range_4
      d hd z w ⟨Nat.le_of_not_gt h120, h150⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_1_range_5
    d hd z w (Nat.le_of_not_gt h150) hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_1

end Fuglede
