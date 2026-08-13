import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 193; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard193 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[4, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 11,
      29, 7,
      1, 0⟩,
    ⟨[4, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 17,
      23, 7,
      1, 0⟩,
    ⟨[4, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 23,
      17, 7,
      1, 0⟩,
    ⟨[4, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      11, 7,
      1, 0⟩,
    ⟨[10, 16, 22, 28, 34, 5], [0, 6, 12, 18, 24, 30],
      0, 7,
      34, 7,
      1, 0⟩,
    ⟨[10, 16, 22, 28, 34, 11], [0, 6, 12, 18, 24, 30],
      0, 13,
      34, 7,
      1, 0⟩,
    ⟨[10, 16, 22, 28, 34, 17], [0, 6, 12, 18, 24, 30],
      0, 19,
      34, 7,
      1, 0⟩,
    ⟨[10, 16, 22, 28, 34, 23], [0, 6, 12, 18, 24, 30],
      0, 25,
      34, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard193 :
    z180K30ExceptionalLiteralWitnessesV87Shard193.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
