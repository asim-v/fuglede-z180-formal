import Fuglede.Z180K18M12CliqueProfileDefs

/-!
Single-value finite leaf for unwanted-order index 2.
The first free clique vertex is the literal `(138 : ZMod 180)`;
there is no quantified first vertex in this theorem.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_z_138 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ w : ZMod 180,
        Z180K18M12UnwantedCommonNeighbor d (138 : ZMod 180) →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 ((138 : ZMod 180) - w) ∈
          z180K18M12EnvelopeOrders →
        (138 : ZMod 180) ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d (138 : ZMod 180) ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  decide

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_z_138

end Fuglede

