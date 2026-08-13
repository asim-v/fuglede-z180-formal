import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 165; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard165 :
    List (RawSet × RawSet) :=
  [
    ([2, 14, 20, 26, 32, 5], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 11], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 17], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 23], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 29], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 35], [0, 6, 12, 18, 24, 30]),
    ([2, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([2, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard165 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard165.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
