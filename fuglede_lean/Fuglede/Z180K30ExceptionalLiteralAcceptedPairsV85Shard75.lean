import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 75; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard75 :
    List (RawSet × RawSet) :=
  [
    ([0, 12, 18, 24, 30, 2], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 24, 30, 8], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 24, 30, 14], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 24, 30, 20], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 24, 30, 26], [0, 6, 12, 18, 24, 30]),
    ([0, 12, 18, 24, 30, 32], [0, 6, 12, 18, 24, 30]),
    ([0, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30]),
    ([0, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard75 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard75.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
