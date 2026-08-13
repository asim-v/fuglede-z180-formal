import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 2 of the fixed missing-order index 0 check.
The first clique vertex satisfies `60 ≤ z.val ∧ z.val < 90`.
Canonical payload SHA-256:
`ac7c38c309f81a06a7da016ff4f652a8a74e9729a8be5cef50800631a469b3e4`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_0_range_2 :
    ∀ z w : ZMod 180,
      60 ≤ z.val ∧ z.val < 90 →
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (0 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (0 : Fin 5) z ≠
        z180K18M12MissingOrderColor (0 : Fin 5) w := by
  decide

#print axioms z180_k18_m12_missingOrderColor_separates_shard_0_range_2

end Fuglede

