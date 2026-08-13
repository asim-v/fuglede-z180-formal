import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 5 of the fixed missing-order index 3 check.
The first clique vertex satisfies `150 ≤ z.val`.
Canonical payload SHA-256:
`985ff576bace51c9799cd6109a1f7bcd07cc444411368c4453ecdb81d665e7a2`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_3_range_5 :
    ∀ z w : ZMod 180,
      150 ≤ z.val →
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (3 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (3 : Fin 5) z ≠
        z180K18M12MissingOrderColor (3 : Fin 5) w := by
  decide

#print axioms z180_k18_m12_missingOrderColor_separates_shard_3_range_5

end Fuglede

