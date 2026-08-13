import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 75; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard75 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 12, 18, 24, 30, 2], [0, 6, 12, 18, 24, 30],
      1, 17,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 8], [0, 6, 12, 18, 24, 30],
      5, 11,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 14], [0, 6, 12, 18, 24, 30],
      1, 11,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 20], [0, 6, 12, 18, 24, 30],
      5, 5,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 26], [0, 6, 12, 18, 24, 30],
      1, 5,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 32], [0, 6, 12, 18, 24, 30],
      5, 17,
      12, 7,
      1, 0⟩,
    ⟨[0, 2, 8, 14, 20, 26], [0, 6, 12, 18, 24, 30],
      1, 1,
      26, 7,
      1, 0⟩,
    ⟨[0, 2, 8, 14, 20, 32], [0, 6, 12, 18, 24, 30],
      5, 1,
      20, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard75 :
    z180K30ExceptionalLiteralWitnessesV87Shard75.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
