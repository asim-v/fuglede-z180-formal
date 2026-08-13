import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 121; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard121 :
    List (RawSet × RawSet) :=
  [
    ([1, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([1, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([1, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([1, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 3], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 9], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 15], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 21], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard121 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard121.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
