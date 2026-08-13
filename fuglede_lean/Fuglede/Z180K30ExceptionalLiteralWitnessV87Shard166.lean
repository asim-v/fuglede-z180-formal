import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 166; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard166 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 1,
      17, 7,
      1, 0⟩,
    ⟨[2, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 11,
      23, 7,
      1, 0⟩,
    ⟨[2, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 7,
      5, 7,
      1, 0⟩,
    ⟨[2, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      35, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 5], [0, 6, 12, 18, 24, 30],
      6, 5,
      8, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 11], [0, 6, 12, 18, 24, 30],
      3, 1,
      32, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 17], [0, 6, 12, 18, 24, 30],
      6, 1,
      32, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 23], [0, 6, 12, 18, 24, 30],
      6, 11,
      8, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard166 :
    z180K30ExceptionalLiteralWitnessesV87Shard166.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
