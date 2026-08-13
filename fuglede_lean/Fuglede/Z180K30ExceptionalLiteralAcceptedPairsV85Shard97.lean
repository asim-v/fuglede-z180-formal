import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 97; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard97 :
    List (RawSet × RawSet) :=
  [
    ([18, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([18, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([18, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([18, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([24, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30]),
    ([24, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30]),
    ([24, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30]),
    ([24, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard97 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard97.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
