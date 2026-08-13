import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 53; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard53 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 10, 22, 34], [6, 9, 12, 18, 24, 30]),
    ([5, 17, 29, 11, 23, 35], [6, 9, 12, 18, 24, 30]),
    ([0, 12, 24, 2, 14, 26], [6, 9, 12, 24, 27, 30]),
    ([0, 12, 24, 10, 22, 34], [6, 9, 12, 24, 27, 30]),
    ([1, 13, 25, 3, 15, 27], [6, 9, 12, 24, 27, 30]),
    ([1, 13, 25, 11, 23, 35], [6, 9, 12, 24, 27, 30]),
    ([2, 14, 26, 4, 16, 28], [6, 9, 12, 24, 27, 30]),
    ([3, 15, 27, 5, 17, 29], [6, 9, 12, 24, 27, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard53 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard53.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
