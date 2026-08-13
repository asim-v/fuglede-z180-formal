import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 189; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard189 :
    List (RawSet × RawSet) :=
  [
    ([4, 10, 16, 22, 28, 5], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 28, 11], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 28, 17], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 28, 23], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 28, 29], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 28, 35], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 34, 5], [0, 6, 12, 18, 24, 30]),
    ([4, 10, 16, 22, 34, 11], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard189 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard189.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
