import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 62; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard62 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 10, 22, 34], [9, 15, 21, 24, 27, 33]),
    ([5, 17, 29, 11, 23, 35], [9, 15, 21, 24, 27, 33]),
    ([0, 12, 24, 6, 18, 30], [9, 15, 21, 27, 30, 33]),
    ([1, 13, 25, 7, 19, 31], [9, 15, 21, 27, 30, 33]),
    ([2, 14, 26, 8, 20, 32], [9, 15, 21, 27, 30, 33]),
    ([3, 15, 27, 9, 21, 33], [9, 15, 21, 27, 30, 33]),
    ([4, 16, 28, 10, 22, 34], [9, 15, 21, 27, 30, 33]),
    ([5, 17, 29, 11, 23, 35], [9, 15, 21, 27, 30, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard62 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard62.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
