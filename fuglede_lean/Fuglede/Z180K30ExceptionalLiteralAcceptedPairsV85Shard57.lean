import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 57; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard57 :
    List (RawSet × RawSet) :=
  [
    ([0, 12, 24, 6, 18, 30], [6, 12, 18, 24, 27, 30]),
    ([1, 13, 25, 7, 19, 31], [6, 12, 18, 24, 27, 30]),
    ([2, 14, 26, 8, 20, 32], [6, 12, 18, 24, 27, 30]),
    ([3, 15, 27, 9, 21, 33], [6, 12, 18, 24, 27, 30]),
    ([4, 16, 28, 10, 22, 34], [6, 12, 18, 24, 27, 30]),
    ([5, 17, 29, 11, 23, 35], [6, 12, 18, 24, 27, 30]),
    ([0, 12, 24, 6, 18, 30], [6, 12, 18, 24, 30, 33]),
    ([1, 13, 25, 7, 19, 31], [6, 12, 18, 24, 30, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard57 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard57.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
