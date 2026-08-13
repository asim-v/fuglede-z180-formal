import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 28; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard28 :
    List (RawSet × RawSet) :=
  [
    ([1, 13, 25, 3, 15, 27], [0, 12, 15, 18, 30, 33]),
    ([1, 13, 25, 11, 23, 35], [0, 12, 15, 18, 30, 33]),
    ([2, 14, 26, 4, 16, 28], [0, 12, 15, 18, 30, 33]),
    ([3, 15, 27, 5, 17, 29], [0, 12, 15, 18, 30, 33]),
    ([4, 16, 28, 6, 18, 30], [0, 12, 15, 18, 30, 33]),
    ([5, 17, 29, 7, 19, 31], [0, 12, 15, 18, 30, 33]),
    ([6, 18, 30, 8, 20, 32], [0, 12, 15, 18, 30, 33]),
    ([7, 19, 31, 9, 21, 33], [0, 12, 15, 18, 30, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard28 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard28.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
