import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 157; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard157 :
    List (RawSet × RawSet) :=
  [
    ([2, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([2, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([2, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([2, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([8, 14, 20, 26, 32, 4], [0, 6, 12, 18, 24, 30]),
    ([8, 14, 20, 26, 32, 10], [0, 6, 12, 18, 24, 30]),
    ([8, 14, 20, 26, 32, 16], [0, 6, 12, 18, 24, 30]),
    ([8, 14, 20, 26, 32, 22], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard157 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard157.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
