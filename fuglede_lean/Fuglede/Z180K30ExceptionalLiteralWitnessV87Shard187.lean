import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 187; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard187 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[21, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 7,
      17, 7,
      1, 0⟩,
    ⟨[21, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 1,
      11, 7,
      1, 0⟩,
    ⟨[21, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 1,
      5, 7,
      1, 0⟩,
    ⟨[21, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 13,
      35, 7,
      1, 0⟩,
    ⟨[27, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      1, 7,
      29, 7,
      1, 0⟩,
    ⟨[27, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      5, 7,
      23, 7,
      1, 0⟩,
    ⟨[27, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 1,
      17, 7,
      1, 0⟩,
    ⟨[27, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 1,
      11, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard187 :
    z180K30ExceptionalLiteralWitnessesV87Shard187.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
