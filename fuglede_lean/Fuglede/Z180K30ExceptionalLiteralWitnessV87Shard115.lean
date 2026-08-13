import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 115; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard115 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[19, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 29,
      26, 7,
      1, 0⟩,
    ⟨[19, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 35,
      20, 7,
      1, 0⟩,
    ⟨[19, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 5,
      14, 7,
      1, 0⟩,
    ⟨[19, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 11,
      8, 7,
      1, 0⟩,
    ⟨[25, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      0, 23,
      2, 7,
      1, 0⟩,
    ⟨[25, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      0, 29,
      32, 7,
      1, 0⟩,
    ⟨[25, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 35,
      26, 7,
      1, 0⟩,
    ⟨[25, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      0, 5,
      20, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard115 :
    z180K30ExceptionalLiteralWitnessesV87Shard115.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
