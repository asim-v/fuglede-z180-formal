import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 107; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard107 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[24, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 19,
      5, 7,
      1, 0⟩,
    ⟨[24, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      35, 7,
      1, 0⟩,
    ⟨[30, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 1,
      29, 7,
      1, 0⟩,
    ⟨[30, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 7,
      23, 7,
      1, 0⟩,
    ⟨[30, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 13,
      17, 7,
      1, 0⟩,
    ⟨[30, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 19,
      11, 7,
      1, 0⟩,
    ⟨[30, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      5, 7,
      1, 0⟩,
    ⟨[30, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard107 :
    z180K30ExceptionalLiteralWitnessesV87Shard107.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
