import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 142; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard142 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[19, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 17,
      29, 7,
      1, 0⟩,
    ⟨[19, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 11,
      23, 7,
      1, 0⟩,
    ⟨[19, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 11,
      17, 7,
      1, 0⟩,
    ⟨[19, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 5,
      11, 7,
      1, 0⟩,
    ⟨[25, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      5, 17,
      5, 7,
      1, 0⟩,
    ⟨[25, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      1, 17,
      35, 7,
      1, 0⟩,
    ⟨[25, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 11,
      29, 7,
      1, 0⟩,
    ⟨[25, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 11,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard142 :
    z180K30ExceptionalLiteralWitnessesV87Shard142.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
