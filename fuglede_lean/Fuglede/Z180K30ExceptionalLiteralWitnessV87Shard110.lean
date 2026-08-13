import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 110; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard110 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 25, 31, 26], [0, 6, 12, 18, 24, 30],
      0, 13,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 32], [0, 6, 12, 18, 24, 30],
      0, 19,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 2], [0, 6, 12, 18, 24, 30],
      0, 31,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 8], [0, 6, 12, 18, 24, 30],
      0, 1,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 14], [0, 6, 12, 18, 24, 30],
      0, 7,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 20], [0, 6, 12, 18, 24, 30],
      0, 13,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 26], [0, 6, 12, 18, 24, 30],
      0, 19,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 32], [0, 6, 12, 18, 24, 30],
      0, 25,
      7, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard110 :
    z180K30ExceptionalLiteralWitnessesV87Shard110.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
