import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 4 of the fixed missing-order index 4 check.
The first clique vertex satisfies `120 ≤ z.val ∧ z.val < 150`.
Canonical payload SHA-256:
`aa8f6cb3de860e074632e2f20d49a1f70bd28c6ba3c0140f962b6971f8c402a2`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_missingOrderColor_separates_shard_4_range_4 :
    ∀ z w : ZMod 180,
      120 ≤ z.val ∧ z.val < 150 →
      frequencyOrder 180 (z - w) ∈ z180K18M12ProfileOrders →
      frequencyOrder 180 (z - w) ≠ z180K18M12RequiredOrder (4 : Fin 5) →
      z ≠ w →
      z180K18M12MissingOrderColor (4 : Fin 5) z ≠
        z180K18M12MissingOrderColor (4 : Fin 5) w := by
  decide

#print axioms z180_k18_m12_missingOrderColor_separates_shard_4_range_4

end Fuglede

