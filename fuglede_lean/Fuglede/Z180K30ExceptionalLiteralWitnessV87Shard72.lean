import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 72; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard72 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 18, 24, 2], [0, 6, 12, 18, 24, 30],
      1, 11,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 8], [0, 6, 12, 18, 24, 30],
      5, 5,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 14], [0, 6, 12, 18, 24, 30],
      1, 5,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 20], [0, 6, 12, 18, 24, 30],
      5, 17,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 26], [0, 6, 12, 18, 24, 30],
      1, 17,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 32], [0, 6, 12, 18, 24, 30],
      5, 11,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 2], [0, 6, 12, 18, 24, 30],
      5, 5,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 8], [0, 6, 12, 18, 24, 30],
      1, 5,
      30, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard72 :
    z180K30ExceptionalLiteralWitnessesV87Shard72.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
