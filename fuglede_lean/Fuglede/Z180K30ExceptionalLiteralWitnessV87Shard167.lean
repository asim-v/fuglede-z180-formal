import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 167; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard167 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[8, 14, 20, 26, 32, 29], [0, 6, 12, 18, 24, 30],
      3, 7,
      32, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      32, 7,
      1, 0⟩,
    ⟨[8, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      3, 1,
      29, 7,
      1, 0⟩,
    ⟨[8, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      6, 1,
      23, 7,
      1, 0⟩,
    ⟨[8, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 11,
      29, 7,
      1, 0⟩,
    ⟨[8, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 7,
      11, 7,
      1, 0⟩,
    ⟨[8, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      5, 7,
      1, 0⟩,
    ⟨[8, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 5,
      11, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard167 :
    z180K30ExceptionalLiteralWitnessesV87Shard167.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
