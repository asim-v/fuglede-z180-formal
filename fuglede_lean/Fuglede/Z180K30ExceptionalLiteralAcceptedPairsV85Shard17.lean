import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 17; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard17 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 10, 22, 34], [0, 6, 12, 18, 21, 30]),
    ([5, 17, 29, 11, 23, 35], [0, 6, 12, 18, 21, 30]),
    ([0, 12, 24, 6, 18, 30], [0, 6, 12, 18, 24, 27]),
    ([1, 13, 25, 7, 19, 31], [0, 6, 12, 18, 24, 27]),
    ([2, 14, 26, 8, 20, 32], [0, 6, 12, 18, 24, 27]),
    ([3, 15, 27, 9, 21, 33], [0, 6, 12, 18, 24, 27]),
    ([4, 16, 28, 10, 22, 34], [0, 6, 12, 18, 24, 27]),
    ([5, 17, 29, 11, 23, 35], [0, 6, 12, 18, 24, 27])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard17 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard17.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
