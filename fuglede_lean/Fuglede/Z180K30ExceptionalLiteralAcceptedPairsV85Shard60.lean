import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 60; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard60 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 6, 18, 30], [9, 12, 15, 27, 30, 33]),
    ([5, 17, 29, 7, 19, 31], [9, 12, 15, 27, 30, 33]),
    ([6, 18, 30, 8, 20, 32], [9, 12, 15, 27, 30, 33]),
    ([7, 19, 31, 9, 21, 33], [9, 12, 15, 27, 30, 33]),
    ([8, 20, 32, 10, 22, 34], [9, 12, 15, 27, 30, 33]),
    ([9, 21, 33, 11, 23, 35], [9, 12, 15, 27, 30, 33]),
    ([0, 12, 24, 6, 18, 30], [9, 15, 18, 21, 27, 33]),
    ([1, 13, 25, 7, 19, 31], [9, 15, 18, 21, 27, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard60 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard60.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
