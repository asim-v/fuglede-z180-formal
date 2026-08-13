import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 141; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard141 :
    List (RawSet × RawSet) :=
  [
    ([13, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([13, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30]),
    ([13, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([13, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([13, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([13, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([19, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([19, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard141 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard141.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
