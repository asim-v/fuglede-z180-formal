import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 124; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard124 :
    List (RawSet × RawSet) :=
  [
    ([19, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([19, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([19, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([19, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([25, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30]),
    ([25, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30]),
    ([25, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30]),
    ([25, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard124 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard124.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
