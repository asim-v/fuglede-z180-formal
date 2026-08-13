import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 139; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard139 :
    List (RawSet × RawSet) :=
  [
    ([1, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([1, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([1, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([1, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 5], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 11], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 17], [0, 6, 12, 18, 24, 30]),
    ([7, 13, 19, 25, 31, 23], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard139 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard139.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
