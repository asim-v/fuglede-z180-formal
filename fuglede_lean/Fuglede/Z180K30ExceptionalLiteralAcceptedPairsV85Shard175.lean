import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 175; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard175 :
    List (RawSet × RawSet) :=
  [
    ([3, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([3, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([3, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([3, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([9, 15, 21, 27, 33, 4], [0, 6, 12, 18, 24, 30]),
    ([9, 15, 21, 27, 33, 10], [0, 6, 12, 18, 24, 30]),
    ([9, 15, 21, 27, 33, 16], [0, 6, 12, 18, 24, 30]),
    ([9, 15, 21, 27, 33, 22], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard175 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard175.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
