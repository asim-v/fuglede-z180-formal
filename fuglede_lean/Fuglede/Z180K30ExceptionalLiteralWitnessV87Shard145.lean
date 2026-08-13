import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 145; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard145 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 8, 14, 20, 32, 15], [0, 6, 12, 18, 24, 30],
      0, 31,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 21], [0, 6, 12, 18, 24, 30],
      0, 1,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 27], [0, 6, 12, 18, 24, 30],
      0, 7,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 33], [0, 6, 12, 18, 24, 30],
      0, 13,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 26, 32, 3], [0, 6, 12, 18, 24, 30],
      0, 25,
      14, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 26, 32, 9], [0, 6, 12, 18, 24, 30],
      0, 31,
      14, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 26, 32, 15], [0, 6, 12, 18, 24, 30],
      0, 1,
      14, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 26, 32, 21], [0, 6, 12, 18, 24, 30],
      0, 7,
      14, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard145 :
    z180K30ExceptionalLiteralWitnessesV87Shard145.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
