import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 180; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard180 :
    List (RawSet × RawSet) :=
  [
    ([3, 9, 15, 21, 27, 5], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 11], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 17], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 23], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 29], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 35], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 33, 5], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 33, 11], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard180 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard180.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
