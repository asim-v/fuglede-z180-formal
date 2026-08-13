import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 104; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard104 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[6, 12, 18, 24, 30, 29], [0, 6, 12, 18, 24, 30],
      0, 23,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      6, 7,
      1, 0⟩,
    ⟨[6, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 13,
      29, 7,
      1, 0⟩,
    ⟨[6, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 19,
      23, 7,
      1, 0⟩,
    ⟨[6, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      17, 7,
      1, 0⟩,
    ⟨[6, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      11, 7,
      1, 0⟩,
    ⟨[6, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 1,
      5, 7,
      1, 0⟩,
    ⟨[6, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 7,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard104 :
    z180K30ExceptionalLiteralWitnessesV87Shard104.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
