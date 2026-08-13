import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 162; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard162 :
    List (RawSet × RawSet) :=
  [
    ([2, 8, 14, 20, 26, 5], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 11], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 17], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 23], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 29], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 26, 35], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 32, 5], [0, 6, 12, 18, 24, 30]),
    ([2, 8, 14, 20, 32, 11], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard162 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard162.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
