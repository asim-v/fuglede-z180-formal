import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 08; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard08 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 10, 22, 34], [0, 3, 12, 18, 24, 30]),
    ([5, 17, 29, 11, 23, 35], [0, 3, 12, 18, 24, 30]),
    ([0, 12, 24, 2, 14, 26], [0, 3, 15, 18, 21, 33]),
    ([0, 12, 24, 10, 22, 34], [0, 3, 15, 18, 21, 33]),
    ([1, 13, 25, 3, 15, 27], [0, 3, 15, 18, 21, 33]),
    ([1, 13, 25, 11, 23, 35], [0, 3, 15, 18, 21, 33]),
    ([2, 14, 26, 4, 16, 28], [0, 3, 15, 18, 21, 33]),
    ([3, 15, 27, 5, 17, 29], [0, 3, 15, 18, 21, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard08 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard08.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
