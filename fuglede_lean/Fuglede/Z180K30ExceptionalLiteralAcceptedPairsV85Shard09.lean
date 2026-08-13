import Fuglede.Z180K30ExceptionalLiteralAcceptedPairsCoreV85

/-! Literal accepted-pair coverage shard 09; no choose/drop reconstruction. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralAcceptedPairsV85Shard09 :
    List (RawSet × RawSet) :=
  [
    ([4, 16, 28, 6, 18, 30], [0, 3, 15, 18, 21, 33]),
    ([5, 17, 29, 7, 19, 31], [0, 3, 15, 18, 21, 33]),
    ([6, 18, 30, 8, 20, 32], [0, 3, 15, 18, 21, 33]),
    ([7, 19, 31, 9, 21, 33], [0, 3, 15, 18, 21, 33]),
    ([8, 20, 32, 10, 22, 34], [0, 3, 15, 18, 21, 33]),
    ([9, 21, 33, 11, 23, 35], [0, 3, 15, 18, 21, 33]),
    ([0, 12, 24, 6, 18, 30], [0, 3, 15, 21, 27, 33]),
    ([1, 13, 25, 7, 19, 31], [0, 3, 15, 21, 27, 33])
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_accepted_pairs_v85_shard09 :
    z180K30ExceptionalLiteralAcceptedPairsV85Shard09.all
      literalExceptionalPairCoveredB_v85 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
