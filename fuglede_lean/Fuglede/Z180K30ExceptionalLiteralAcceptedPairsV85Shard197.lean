import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 197; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard197 :
    List (RawSet × RawSet) :=
  [
    ([28, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([28, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([34, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([34, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30]),
    ([34, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([34, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([34, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([34, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard197 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard197.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
