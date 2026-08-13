import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 0 of the fixed missing-order index 1 check.
The first clique vertex satisfies `z.val < 30`.
Canonical payload SHA-256:
`390a1c428b030dac5df5ea60751afed83ba5096f1b1181fd482476218615025c`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_1_range_0 :
    ∀ z w : ZMod 180,
      z.val < 30 →
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (1 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (1 : Fin 5) z ≠
        z180K18M12MissingOrderColor (1 : Fin 5) w := by
  decide

#print axioms z180_k18_m12_missingOrderColor_separates_shard_1_range_0

end Fuglede

