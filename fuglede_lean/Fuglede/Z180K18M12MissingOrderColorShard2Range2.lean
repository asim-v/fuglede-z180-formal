import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 2 of the fixed missing-order index 2 check.
The first clique vertex satisfies `60 ≤ z.val ∧ z.val < 90`.
Canonical payload SHA-256:
`e3936fa7f3f3ab47d4ac3f3673b26f6a8d6ab1429261d88c38e7adf2605cf0eb`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_2_range_2 :
    ∀ z w : ZMod 180,
      60 ≤ z.val ∧ z.val < 90 →
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (2 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (2 : Fin 5) z ≠
        z180K18M12MissingOrderColor (2 : Fin 5) w := by
  decide

#print axioms z180_k18_m12_missingOrderColor_separates_shard_2_range_2

end Fuglede

