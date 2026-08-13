import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 100; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard100 :
    List (RawSet × RawSet) :=
  [
    ([0, 6, 12, 18, 30, 17], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 23], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 29], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 35], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 5], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 11], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 17], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 23], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard100 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard100.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
