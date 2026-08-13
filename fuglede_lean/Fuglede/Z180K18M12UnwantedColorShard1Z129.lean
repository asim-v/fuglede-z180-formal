import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Single-value finite leaf for unwanted-order index 1.
The first free clique vertex is the literal `(129 : ZMod 180)`;
there is no quantified first vertex in this theorem.
Canonical payload SHA-256:
`d497e6d95567eb73a6eab6dd04a2d54a2f7e861e341ab14cf65c6573713aabe1`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_1_z_129 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (1 : Fin 3) →
      ∀ w : ZMod 180,
        Z180K18M12UnwantedCommonNeighbor d (129 : ZMod 180) →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 ((129 : ZMod 180) - w) ∈
          z180K18M12EnvelopeOrders →
        (129 : ZMod 180) ≠ w →
        z180K18M12UnwantedColor (1 : Fin 3) d (129 : ZMod 180) ≠
          z180K18M12UnwantedColor (1 : Fin 3) d w := by
  decide

#print axioms z180_k18_m12_unwantedColor_separates_shard_1_z_129

end Fuglede

