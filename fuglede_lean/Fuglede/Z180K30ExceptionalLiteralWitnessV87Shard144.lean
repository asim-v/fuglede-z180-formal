import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 144; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard144 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 8, 14, 20, 26, 3], [0, 6, 12, 18, 24, 30],
      0, 13,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 9], [0, 6, 12, 18, 24, 30],
      0, 19,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 15], [0, 6, 12, 18, 24, 30],
      0, 25,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 21], [0, 6, 12, 18, 24, 30],
      0, 31,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 27], [0, 6, 12, 18, 24, 30],
      0, 1,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 33], [0, 6, 12, 18, 24, 30],
      0, 7,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 3], [0, 6, 12, 18, 24, 30],
      0, 19,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 9], [0, 6, 12, 18, 24, 30],
      0, 25,
      20, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard144 :
    z180K30ExceptionalLiteralWitnessesV87Shard144.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
