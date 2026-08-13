import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 192; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard192 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 22, 28, 34, 5], [0, 6, 12, 18, 24, 30]),
    ([4, 16, 22, 28, 34, 11], [0, 6, 12, 18, 24, 30]),
    ([4, 16, 22, 28, 34, 17], [0, 6, 12, 18, 24, 30]),
    ([4, 16, 22, 28, 34, 23], [0, 6, 12, 18, 24, 30]),
    ([4, 16, 22, 28, 34, 29], [0, 6, 12, 18, 24, 30]),
    ([4, 16, 22, 28, 34, 35], [0, 6, 12, 18, 24, 30]),
    ([4, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30]),
    ([4, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard192 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard192.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
