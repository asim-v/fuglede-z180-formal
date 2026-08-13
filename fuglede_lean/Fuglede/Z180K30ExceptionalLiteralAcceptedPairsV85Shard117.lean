import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 117; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard117 :
    List (RawSet × RawSet) :=
  [
    ([1, 7, 13, 19, 25, 3], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 9], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 15], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 21], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 27], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 33], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 3], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 9], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard117 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard117.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
