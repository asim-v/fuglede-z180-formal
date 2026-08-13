import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 34; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard34 :
    List (RawSet × RawSet) :=
  [
    ([1, 13, 25, 3, 15, 27], [3, 6, 9, 21, 24, 27]),
    ([1, 13, 25, 11, 23, 35], [3, 6, 9, 21, 24, 27]),
    ([2, 14, 26, 4, 16, 28], [3, 6, 9, 21, 24, 27]),
    ([3, 15, 27, 5, 17, 29], [3, 6, 9, 21, 24, 27]),
    ([4, 16, 28, 6, 18, 30], [3, 6, 9, 21, 24, 27]),
    ([5, 17, 29, 7, 19, 31], [3, 6, 9, 21, 24, 27]),
    ([6, 18, 30, 8, 20, 32], [3, 6, 9, 21, 24, 27]),
    ([7, 19, 31, 9, 21, 33], [3, 6, 9, 21, 24, 27])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard34 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard34.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
