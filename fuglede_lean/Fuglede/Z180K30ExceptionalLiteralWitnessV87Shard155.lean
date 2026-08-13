import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 155; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard155 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 8, 14, 26, 32, 28], [0, 6, 12, 18, 24, 30],
      1, 11,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 26, 32, 34], [0, 6, 12, 18, 24, 30],
      5, 5,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 4], [0, 6, 12, 18, 24, 30],
      5, 17,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 10], [0, 6, 12, 18, 24, 30],
      1, 17,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 16], [0, 6, 12, 18, 24, 30],
      5, 11,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 22], [0, 6, 12, 18, 24, 30],
      1, 11,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 28], [0, 6, 12, 18, 24, 30],
      5, 5,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 20, 26, 32, 34], [0, 6, 12, 18, 24, 30],
      1, 5,
      20, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard155 :
    z180K30ExceptionalLiteralWitnessesV87Shard155.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
