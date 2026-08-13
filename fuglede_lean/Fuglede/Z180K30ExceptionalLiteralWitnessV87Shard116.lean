import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 116; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard116 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[25, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 11,
      14, 7,
      1, 0⟩,
    ⟨[25, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 17,
      8, 7,
      1, 0⟩,
    ⟨[31, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      0, 29,
      2, 7,
      1, 0⟩,
    ⟨[31, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      0, 35,
      32, 7,
      1, 0⟩,
    ⟨[31, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 5,
      26, 7,
      1, 0⟩,
    ⟨[31, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 11,
      20, 7,
      1, 0⟩,
    ⟨[31, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 17,
      14, 7,
      1, 0⟩,
    ⟨[31, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 23,
      8, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard116 :
    z180K30ExceptionalLiteralWitnessesV87Shard116.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
