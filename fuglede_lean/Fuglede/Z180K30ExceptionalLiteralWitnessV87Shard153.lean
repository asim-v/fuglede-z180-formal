import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 153; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard153 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 8, 14, 20, 26, 4], [0, 6, 12, 18, 24, 30],
      1, 11,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 10], [0, 6, 12, 18, 24, 30],
      5, 5,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 16], [0, 6, 12, 18, 24, 30],
      1, 5,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 22], [0, 6, 12, 18, 24, 30],
      5, 17,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 28], [0, 6, 12, 18, 24, 30],
      1, 17,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 34], [0, 6, 12, 18, 24, 30],
      5, 11,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 4], [0, 6, 12, 18, 24, 30],
      5, 5,
      32, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 10], [0, 6, 12, 18, 24, 30],
      1, 5,
      32, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard153 :
    z180K30ExceptionalLiteralWitnessesV87Shard153.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
