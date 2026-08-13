import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 143; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard143 :
    List (RawSet × RawSet) :=
  [
    ([25, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([25, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([31, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([31, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30]),
    ([31, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([31, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([31, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([31, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard143 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard143.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
