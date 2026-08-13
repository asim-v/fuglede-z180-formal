import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 71; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard71 :
    List (RawSet × RawSet) :=
  [
    ([24, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([24, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([30, 1, 7, 13, 19, 25], [0, 6, 12, 18, 24, 30]),
    ([30, 1, 7, 13, 19, 31], [0, 6, 12, 18, 24, 30]),
    ([30, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([30, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([30, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([30, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard71 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard71.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
