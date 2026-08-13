import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 168; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard168 :
    List (RawSet × RawSet) :=
  [
    ([14, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([14, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30]),
    ([14, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([14, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([14, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([14, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([20, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([20, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard168 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard168.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
