import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 188; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard188 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[27, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 13,
      5, 7,
      1, 0⟩,
    ⟨[27, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 13,
      35, 7,
      1, 0⟩,
    ⟨[33, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      5, 7,
      29, 7,
      1, 0⟩,
    ⟨[33, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      1, 1,
      23, 7,
      1, 0⟩,
    ⟨[33, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 1,
      17, 7,
      1, 0⟩,
    ⟨[33, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 13,
      11, 7,
      1, 0⟩,
    ⟨[33, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 13,
      5, 7,
      1, 0⟩,
    ⟨[33, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 7,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard188 :
    z180K30ExceptionalLiteralWitnessesV87Shard188.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
