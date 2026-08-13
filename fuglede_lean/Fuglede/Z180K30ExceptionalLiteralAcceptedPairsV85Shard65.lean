import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 65; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard65 :
    List (RawSet × RawSet) :=
  [
    ([0, 6, 12, 24, 30, 25], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 31], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 1], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 7], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 13], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 19], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 25], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 18, 24, 30, 31], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard65 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard65.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
