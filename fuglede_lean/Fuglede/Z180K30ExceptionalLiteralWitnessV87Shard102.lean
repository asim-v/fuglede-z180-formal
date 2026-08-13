import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 102; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard102 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 12, 18, 24, 30, 5], [0, 6, 12, 18, 24, 30],
      0, 29,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 11], [0, 6, 12, 18, 24, 30],
      0, 35,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 17], [0, 6, 12, 18, 24, 30],
      0, 5,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 23], [0, 6, 12, 18, 24, 30],
      0, 11,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 29], [0, 6, 12, 18, 24, 30],
      0, 17,
      12, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 35], [0, 6, 12, 18, 24, 30],
      0, 23,
      12, 7,
      1, 0⟩,
    ⟨[0, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 7,
      29, 7,
      1, 0⟩,
    ⟨[0, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 13,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard102 :
    z180K30ExceptionalLiteralWitnessesV87Shard102.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
