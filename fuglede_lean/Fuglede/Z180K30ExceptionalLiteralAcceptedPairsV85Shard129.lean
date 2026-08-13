import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 129; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard129 :
    List (RawSet × RawSet) :=
  [
    ([1, 13, 19, 25, 31, 4], [0, 6, 12, 18, 24, 30]),
    ([1, 13, 19, 25, 31, 10], [0, 6, 12, 18, 24, 30]),
    ([1, 13, 19, 25, 31, 16], [0, 6, 12, 18, 24, 30]),
    ([1, 13, 19, 25, 31, 22], [0, 6, 12, 18, 24, 30]),
    ([1, 13, 19, 25, 31, 28], [0, 6, 12, 18, 24, 30]),
    ([1, 13, 19, 25, 31, 34], [0, 6, 12, 18, 24, 30]),
    ([1, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30]),
    ([1, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard129 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard129.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
