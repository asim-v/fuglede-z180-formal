import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 91; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard91 :
    List (RawSet × RawSet) :=
  [
    ([0, 6, 12, 18, 30, 16], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 22], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 28], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 18, 30, 34], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 4], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 10], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 16], [0, 6, 12, 18, 24, 30]),
    ([0, 6, 12, 24, 30, 22], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard91 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard91.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
