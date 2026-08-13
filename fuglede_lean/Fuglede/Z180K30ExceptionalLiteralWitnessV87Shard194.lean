import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 194; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard194 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[10, 16, 22, 28, 34, 29], [0, 6, 12, 18, 24, 30],
      0, 31,
      34, 7,
      1, 0⟩,
    ⟨[10, 16, 22, 28, 34, 35], [0, 6, 12, 18, 24, 30],
      0, 1,
      34, 7,
      1, 0⟩,
    ⟨[10, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 5,
      5, 7,
      1, 0⟩,
    ⟨[10, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 11,
      35, 7,
      1, 0⟩,
    ⟨[10, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 17,
      29, 7,
      1, 0⟩,
    ⟨[10, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 23,
      23, 7,
      1, 0⟩,
    ⟨[10, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      17, 7,
      1, 0⟩,
    ⟨[10, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 35,
      11, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard194 :
    z180K30ExceptionalLiteralWitnessesV87Shard194.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
