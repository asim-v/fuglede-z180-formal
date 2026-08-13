import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 79; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard79 :
    List (RawSet × RawSet) :=
  [
    ([18, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([18, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([18, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([18, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([24, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30]),
    ([24, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30]),
    ([24, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([24, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard79 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard79.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
