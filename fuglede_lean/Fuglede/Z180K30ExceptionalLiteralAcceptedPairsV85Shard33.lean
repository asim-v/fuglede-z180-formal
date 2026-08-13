import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 33; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard33 :
    List (RawSet × RawSet) :=
  [
    ([0, 12, 24, 6, 18, 30], [3, 6, 9, 15, 27, 33]),
    ([1, 13, 25, 7, 19, 31], [3, 6, 9, 15, 27, 33]),
    ([2, 14, 26, 8, 20, 32], [3, 6, 9, 15, 27, 33]),
    ([3, 15, 27, 9, 21, 33], [3, 6, 9, 15, 27, 33]),
    ([4, 16, 28, 10, 22, 34], [3, 6, 9, 15, 27, 33]),
    ([5, 17, 29, 11, 23, 35], [3, 6, 9, 15, 27, 33]),
    ([0, 12, 24, 2, 14, 26], [3, 6, 9, 21, 24, 27]),
    ([0, 12, 24, 10, 22, 34], [3, 6, 9, 21, 24, 27])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard33 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard33.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
