import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12MissingOrderColorShard1Range0
import Fuglede.Z180K18M12MissingOrderColorShard1Range1
import Fuglede.Z180K18M12MissingOrderColorShard1Range2
import Fuglede.Z180K18M12MissingOrderColorShard1Range3
import Fuglede.Z180K18M12MissingOrderColorShard1Range4
import Fuglede.Z180K18M12MissingOrderColorShard1Range5

/-!
Fixed-index aggregator for a missing order `9`.  The six finite
checks are disjoint first-vertex ranges of width thirty; this module contains
no `decide` proof.
Payload SHA-256:
`390a1c428b030dac5df5ea60751afed83ba5096f1b1181fd482476218615025c`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_1 :
    ∀ z w : ZMod 180,
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (1 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (1 : Fin 5) z ≠
        z180K18M12MissingOrderColor (1 : Fin 5) w := by
  intro z w hprofile hmissing hne
  by_cases h30 : z.val < 30
  · exact z180_k18_m12_missingOrderColor_separates_shard_1_range_0
      z w h30 hprofile hmissing hne
  by_cases h60 : z.val < 60
  · exact z180_k18_m12_missingOrderColor_separates_shard_1_range_1
      z w ⟨by omega, h60⟩ hprofile hmissing hne
  by_cases h90 : z.val < 90
  · exact z180_k18_m12_missingOrderColor_separates_shard_1_range_2
      z w ⟨by omega, h90⟩ hprofile hmissing hne
  by_cases h120 : z.val < 120
  · exact z180_k18_m12_missingOrderColor_separates_shard_1_range_3
      z w ⟨by omega, h120⟩ hprofile hmissing hne
  by_cases h150 : z.val < 150
  · exact z180_k18_m12_missingOrderColor_separates_shard_1_range_4
      z w ⟨by omega, h150⟩ hprofile hmissing hne
  exact z180_k18_m12_missingOrderColor_separates_shard_1_range_5
    z w (by omega) hprofile hmissing hne

#print axioms z180_k18_m12_missingOrderColor_separates_shard_1

end Fuglede
