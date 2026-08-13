import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 185; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard185 :
    List (RawSet × RawSet) :=
  [
    ([9, 15, 21, 27, 33, 29], [0, 6, 12, 18, 24, 30]),
    ([9, 15, 21, 27, 33, 35], [0, 6, 12, 18, 24, 30]),
    ([9, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([9, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30]),
    ([9, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([9, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([9, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([9, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard185 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard185.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
