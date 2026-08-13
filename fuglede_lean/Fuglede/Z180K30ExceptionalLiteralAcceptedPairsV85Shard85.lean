import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 85; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard85 :
    List (RawSet × RawSet) :=
  [
    ([0, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([0, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([0, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([0, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 3], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 9], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 15], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 21], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard85 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard85.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
