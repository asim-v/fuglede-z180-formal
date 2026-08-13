import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 74; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard74 :
    List (RawSet × RawSet) :=
  [
    ([0, 6, 12, 24, 30, 26], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 32], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 2], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 8], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 14], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 20], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 26], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 32], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard74 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard74.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
