import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 165; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard165 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 14, 20, 26, 32, 5], [0, 6, 12, 18, 24, 30],
      6, 7,
      2, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 11], [0, 6, 12, 18, 24, 30],
      6, 5,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 17], [0, 6, 12, 18, 24, 30],
      3, 1,
      2, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 23], [0, 6, 12, 18, 24, 30],
      6, 1,
      2, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 29], [0, 6, 12, 18, 24, 30],
      6, 11,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 35], [0, 6, 12, 18, 24, 30],
      3, 7,
      2, 7,
      1, 0⟩,
    ⟨[2, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      6, 5,
      5, 7,
      1, 0⟩,
    ⟨[2, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      3, 1,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard165 :
    z180K30ExceptionalLiteralWitnessesV87Shard165.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
