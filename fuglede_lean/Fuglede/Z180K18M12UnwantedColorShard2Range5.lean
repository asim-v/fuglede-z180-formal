import Fuglede.Z180K18M12CliqueProfileDefs
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice0
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice1
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice2
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice3
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice4
import Fuglede.Z180K18M12UnwantedColorShard2Range5Slice5

/-!
Proof-only width-thirty range aggregator 5 for unwanted-order index 2.
Its six width-five slices contain the finite `decide` checks; this module
contains no `decide` and only dispatches by first-vertex bounds.
Canonical payload SHA-256:
`5322fc775e9236c2485129b0a1edb58c496a41768df5bbd666d0b1dd476d935a`
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m12_unwantedColor_separates_shard_2_range_5 :
    ∀ d : ZMod 180,
      frequencyOrder 180 d = z180K18M12UnwantedOrder (2 : Fin 3) →
      ∀ z w : ZMod 180,
        150 ≤ z.val →
        Z180K18M12UnwantedCommonNeighbor d z →
        Z180K18M12UnwantedCommonNeighbor d w →
        frequencyOrder 180 (z - w) ∈ z180K18M12EnvelopeOrders →
        z ≠ w →
        z180K18M12UnwantedColor (2 : Fin 3) d z ≠
          z180K18M12UnwantedColor (2 : Fin 3) d w := by
  intro d hd z w hzRange hz hw hzw hne
  by_cases h155 : z.val < 155
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_0
      d hd z w ⟨hzRange, h155⟩ hz hw hzw hne
  by_cases h160 : z.val < 160
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_1
      d hd z w ⟨Nat.le_of_not_gt h155, h160⟩ hz hw hzw hne
  by_cases h165 : z.val < 165
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_2
      d hd z w ⟨Nat.le_of_not_gt h160, h165⟩ hz hw hzw hne
  by_cases h170 : z.val < 170
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_3
      d hd z w ⟨Nat.le_of_not_gt h165, h170⟩ hz hw hzw hne
  by_cases h175 : z.val < 175
  · exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_4
      d hd z w ⟨Nat.le_of_not_gt h170, h175⟩ hz hw hzw hne
  exact z180_k18_m12_unwantedColor_separates_shard_2_range_5_slice_5
    d hd z w (Nat.le_of_not_gt h175) hz hw hzw hne

#print axioms z180_k18_m12_unwantedColor_separates_shard_2_range_5

end Fuglede
