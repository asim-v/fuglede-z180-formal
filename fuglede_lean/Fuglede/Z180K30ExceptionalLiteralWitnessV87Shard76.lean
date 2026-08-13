import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 76; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard76 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 2, 8, 14, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 13,
      14, 7,
      1, 0⟩,
    ⟨[0, 2, 8, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 13,
      8, 7,
      1, 0⟩,
    ⟨[0, 2, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      1, 7,
      2, 7,
      1, 0⟩,
    ⟨[0, 8, 14, 20, 26, 32], [0, 6, 12, 18, 24, 30],
      5, 7,
      32, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 2], [0, 6, 12, 18, 24, 30],
      5, 11,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 8], [0, 6, 12, 18, 24, 30],
      1, 11,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 14], [0, 6, 12, 18, 24, 30],
      5, 5,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 20], [0, 6, 12, 18, 24, 30],
      1, 5,
      6, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard76 :
    z180K30ExceptionalLiteralWitnessesV87Shard76.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
