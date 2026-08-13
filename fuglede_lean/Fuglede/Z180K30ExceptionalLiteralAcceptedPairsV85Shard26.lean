import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 26; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard26 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 10, 22, 34], [0, 9, 12, 18, 24, 30]),
    ([5, 17, 29, 11, 23, 35], [0, 9, 12, 18, 24, 30]),
    ([0, 12, 24, 6, 18, 30], [0, 9, 15, 21, 27, 33]),
    ([1, 13, 25, 7, 19, 31], [0, 9, 15, 21, 27, 33]),
    ([2, 14, 26, 8, 20, 32], [0, 9, 15, 21, 27, 33]),
    ([3, 15, 27, 9, 21, 33], [0, 9, 15, 21, 27, 33]),
    ([4, 16, 28, 10, 22, 34], [0, 9, 15, 21, 27, 33]),
    ([5, 17, 29, 11, 23, 35], [0, 9, 15, 21, 27, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard26 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard26.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
