import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 126; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard126 :
    List (RawSet × RawSet) :=
  [
    ([1, 7, 13, 19, 25, 4], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 10], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 16], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 22], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 28], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 25, 34], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 4], [0, 6, 12, 18, 24, 30]),
    ([1, 7, 13, 19, 31, 10], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard126 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard126.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
