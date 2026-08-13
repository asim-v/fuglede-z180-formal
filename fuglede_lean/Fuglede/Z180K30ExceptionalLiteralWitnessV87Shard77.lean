import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 77; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard77 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[6, 12, 18, 24, 30, 26], [0, 6, 12, 18, 24, 30],
      5, 17,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 32], [0, 6, 12, 18, 24, 30],
      1, 17,
      6, 7,
      1, 0⟩,
    ⟨[6, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      5, 1,
      26, 7,
      1, 0⟩,
    ⟨[6, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      1, 13,
      20, 7,
      1, 0⟩,
    ⟨[6, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 13,
      14, 7,
      1, 0⟩,
    ⟨[6, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 7,
      8, 7,
      1, 0⟩,
    ⟨[6, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 7,
      2, 7,
      1, 0⟩,
    ⟨[6, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 1,
      32, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard77 :
    z180K30ExceptionalLiteralWitnessesV87Shard77.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
