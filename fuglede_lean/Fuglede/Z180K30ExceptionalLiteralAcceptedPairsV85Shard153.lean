import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 153; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard153 :
    List (RawSet × RawSet) :=
  [
    ([2, 8, 14, 20, 26, 4], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 10], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 16], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 22], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 28], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 34], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 32, 4], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 32, 10], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard153 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard153.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
