import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 80; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard80 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[24, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 13,
      2, 7,
      1, 0⟩,
    ⟨[24, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 13,
      32, 7,
      1, 0⟩,
    ⟨[30, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      5, 7,
      26, 7,
      1, 0⟩,
    ⟨[30, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      1, 1,
      20, 7,
      1, 0⟩,
    ⟨[30, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 1,
      14, 7,
      1, 0⟩,
    ⟨[30, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 13,
      8, 7,
      1, 0⟩,
    ⟨[30, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 13,
      2, 7,
      1, 0⟩,
    ⟨[30, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 7,
      32, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard80 :
    z180K30ExceptionalLiteralWitnessesV87Shard80.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
