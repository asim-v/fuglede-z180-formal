import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 112; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard112 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 11,
      26, 7,
      1, 0⟩,
    ⟨[1, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 17,
      20, 7,
      1, 0⟩,
    ⟨[1, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 23,
      14, 7,
      1, 0⟩,
    ⟨[1, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 29,
      8, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 2], [0, 6, 12, 18, 24, 30],
      0, 7,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 8], [0, 6, 12, 18, 24, 30],
      0, 13,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 14], [0, 6, 12, 18, 24, 30],
      0, 19,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 20], [0, 6, 12, 18, 24, 30],
      0, 25,
      31, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard112 :
    z180K30ExceptionalLiteralWitnessesV87Shard112.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
