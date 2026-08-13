import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 73; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard73 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 18, 30, 14], [0, 6, 12, 18, 24, 30],
      5, 17,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 20], [0, 6, 12, 18, 24, 30],
      1, 17,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 26], [0, 6, 12, 18, 24, 30],
      5, 11,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 32], [0, 6, 12, 18, 24, 30],
      1, 11,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 2], [0, 6, 12, 18, 24, 30],
      1, 5,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 8], [0, 6, 12, 18, 24, 30],
      5, 17,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 14], [0, 6, 12, 18, 24, 30],
      1, 17,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 20], [0, 6, 12, 18, 24, 30],
      5, 11,
      24, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard73 :
    z180K30ExceptionalLiteralWitnessesV87Shard73.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
