import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 182; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard182 :
    List (RawSet × RawSet) :=
  [
    ([3, 9, 15, 27, 33, 29], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 27, 33, 35], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 5], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 11], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 17], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 23], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 29], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 21, 27, 33, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard182 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard182.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
