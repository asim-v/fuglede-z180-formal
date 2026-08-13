import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 135; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard135 :
    List (RawSet × RawSet) :=
  [
    ([1, 7, 13, 19, 25, 5], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 11], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 17], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 23], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 29], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 35], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 5], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 11], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard135 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard135.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
