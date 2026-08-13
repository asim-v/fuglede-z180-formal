import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 171; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard171 :
    List (RawSet × RawSet) :=
  [
    ([3, 9, 15, 21, 27, 4], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 10], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 16], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 22], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 28], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 27, 34], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 33, 4], [0, 6, 12, 18, 24, 30]),
    ([3, 9, 15, 21, 33, 10], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard171 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard171.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
