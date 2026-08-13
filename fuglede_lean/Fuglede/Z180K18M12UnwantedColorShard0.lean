import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard0Range0
import Fuglede.Z180K18M12UnwantedColorShard0Range1
import Fuglede.Z180K18M12UnwantedColorShard0Range2
import Fuglede.Z180K18M12UnwantedColorShard0Range3
import Fuglede.Z180K18M12UnwantedColorShard0Range4
import Fuglede.Z180K18M12UnwantedColorShard0Range5

/-!
Fixed-index aggregator for unwanted order `2`.  The six finite
checks are disjoint first-vertex ranges of width thirty; this module contains
no `decide` proof.
Payload SHA-256:
`3abbf7c94f87be8d8a176f0c29d5221b5e7cb803a38d9390a93c24fa237c22c9`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_0 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (0 : Fin 3) →
      ∀ z w : ZMod 180,
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (0 : Fin 3) d z ≠
          z180K18M12UnwantedColor (0 : Fin 3) d w := by
  intro d hd z w hz hw hzw hne
  by_cases h30 : z.val < 30
  · exact z180_k18_m12_unwantedColor_separates_shard_0_range_0
      d hd z w h30 hz hw hzw hne
  by_cases h60 : z.val < 60
  · exact z180_k18_m12_unwantedColor_separates_shard_0_range_1
      d hd z w ⟨by omega, h60⟩ hz hw hzw hne
  by_cases h90 : z.val < 90
  · exact z180_k18_m12_unwantedColor_separates_shard_0_range_2
      d hd z w ⟨by omega, h90⟩ hz hw hzw hne
  by_cases h120 : z.val < 120
  · exact z180_k18_m12_unwantedColor_separates_shard_0_range_3
      d hd z w ⟨by omega, h120⟩ hz hw hzw hne
  by_cases h150 : z.val < 150
  · exact z180_k18_m12_unwantedColor_separates_shard_0_range_4
      d hd z w ⟨by omega, h150⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_0_range_5
    d hd z w (by omega) hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_0

end Fuglede
