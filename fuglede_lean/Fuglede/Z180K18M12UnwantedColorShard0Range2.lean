import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Range subshard 2 of the fixed unwanted-order index 0 check.
The first free clique vertex satisfies `60 ≤ z.val ∧ z.val < 90`.
Canonical payload SHA-256:
`3abbf7c94f87be8d8a176f0c29d5221b5e7cb803a38d9390a93c24fa237c22c9`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_0_range_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (0 : Fin 3) →
      ∀ z w : ZMod 180,
        60 ≤ z.val ∧ z.val < 90 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (0 : Fin 3) d z ≠
          z180K18M12UnwantedColor (0 : Fin 3) d w := by
  decide

#print axioms z180_k18_m12_unwantedColor_separates_shard_0_range_2

end Fuglede

