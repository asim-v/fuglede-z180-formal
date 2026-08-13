import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 123; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard123 :
    List (RawSet × RawSet) :=
  [
    ([13, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30]),
    ([13, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30]),
    ([13, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([13, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([13, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([13, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([19, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30]),
    ([19, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard123 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard123.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
