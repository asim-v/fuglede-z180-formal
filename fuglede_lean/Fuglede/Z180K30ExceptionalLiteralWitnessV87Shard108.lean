import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 108; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard108 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 19, 25, 2], [0, 6, 12, 18, 24, 30],
      0, 13,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 8], [0, 6, 12, 18, 24, 30],
      0, 19,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 14], [0, 6, 12, 18, 24, 30],
      0, 25,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 20], [0, 6, 12, 18, 24, 30],
      0, 31,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 26], [0, 6, 12, 18, 24, 30],
      0, 1,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 32], [0, 6, 12, 18, 24, 30],
      0, 7,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 2], [0, 6, 12, 18, 24, 30],
      0, 19,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 8], [0, 6, 12, 18, 24, 30],
      0, 25,
      19, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard108 :
    z180K30ExceptionalLiteralWitnessesV87Shard108.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
