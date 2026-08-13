import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 156; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard156 :
    List (RawSet × RawSet) :=
  [
    ([2, 14, 20, 26, 32, 4], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 10], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 16], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 22], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 28], [0, 6, 12, 18, 24, 30]),
    ([2, 14, 20, 26, 32, 34], [0, 6, 12, 18, 24, 30]),
    ([2, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30]),
    ([2, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard156 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard156.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
