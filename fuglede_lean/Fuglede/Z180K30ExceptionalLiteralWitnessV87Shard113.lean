import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 113; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard113 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[7, 13, 19, 25, 31, 26], [0, 6, 12, 18, 24, 30],
      0, 31,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 32], [0, 6, 12, 18, 24, 30],
      0, 1,
      31, 7,
      1, 0⟩,
    ⟨[7, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      0, 5,
      2, 7,
      1, 0⟩,
    ⟨[7, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      0, 11,
      32, 7,
      1, 0⟩,
    ⟨[7, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 17,
      26, 7,
      1, 0⟩,
    ⟨[7, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 23,
      20, 7,
      1, 0⟩,
    ⟨[7, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 29,
      14, 7,
      1, 0⟩,
    ⟨[7, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 35,
      8, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard113 :
    z180K30ExceptionalLiteralWitnessesV87Shard113.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
