import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 112; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard112 :
    List (RawSet × RawSet) :=
  [
    ([1, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([1, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([1, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([1, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 2], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 8], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 14], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 20], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard112 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard112.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
