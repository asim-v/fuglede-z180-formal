import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 67; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard67 :
    List (RawSet × RawSet) :=
  [
    ([0, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([0, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([0, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([0, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 1], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 7], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 13], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 19], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard67 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard67.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
