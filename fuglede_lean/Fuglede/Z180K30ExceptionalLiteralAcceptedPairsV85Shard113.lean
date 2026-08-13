import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 113; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard113 :
    List (RawSet × RawSet) :=
  [
    ([7, 13, 19, 25, 31, 26], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30]),
    ([7, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30]),
    ([7, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard113 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard113.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
