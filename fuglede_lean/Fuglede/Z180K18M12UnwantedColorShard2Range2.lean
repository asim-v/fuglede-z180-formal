import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice0
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice1
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice2
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice3
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice4
import Fuglede.Z180K18M12UnwantedColorShard2Range2Slice5

/-!
Proof-only width-thirty range aggregator 2 for unwanted-order index 2.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_2 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        60 ≤ z.val ∧ z.val < 90 →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h65 : z.val < 65
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_0
      d hd z w ⟨hzRange.1, h65⟩ hz hw hzw hne
  by_cases h70 : z.val < 70
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_1
      d hd z w ⟨Nat.le_of_not_gt h65, h70⟩ hz hw hzw hne
  by_cases h75 : z.val < 75
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_2
      d hd z w ⟨Nat.le_of_not_gt h70, h75⟩ hz hw hzw hne
  by_cases h80 : z.val < 80
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_3
      d hd z w ⟨Nat.le_of_not_gt h75, h80⟩ hz hw hzw hne
  by_cases h85 : z.val < 85
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_4
      d hd z w ⟨Nat.le_of_not_gt h80, h85⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_2_range_2_slice_5
    d hd z w ⟨Nat.le_of_not_gt h85, hzRange.2⟩ hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_2

end Fuglede

