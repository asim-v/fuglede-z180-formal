import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 90; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard90 :
    List (RawSet × RawSet) :=
  [
    ([0, 6, 12, 18, 24, 4], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 10], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 16], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 22], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 28], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 24, 34], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 4], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 10], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard90 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard90.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
