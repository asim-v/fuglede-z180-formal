import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 103; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard103 :
    List (RawSet × RawSet) :=
  [
    ([0, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([0, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([0, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([0, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 5], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 11], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 17], [0, 6, 12, 18, 24, 30]),
    ([6, 12, 18, 24, 30, 23], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard103 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard103.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
