import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 196; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard196 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[22, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      29, 7,
      1, 0⟩,
    ⟨[22, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 35,
      23, 7,
      1, 0⟩,
    ⟨[22, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 5,
      17, 7,
      1, 0⟩,
    ⟨[22, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 11,
      11, 7,
      1, 0⟩,
    ⟨[28, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 23,
      5, 7,
      1, 0⟩,
    ⟨[28, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      35, 7,
      1, 0⟩,
    ⟨[28, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 35,
      29, 7,
      1, 0⟩,
    ⟨[28, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 5,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard196 :
    z180K30ExceptionalLiteralWitnessesV87Shard196.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
