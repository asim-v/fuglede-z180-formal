import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 105; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard105 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[12, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 19,
      29, 7,
      1, 0⟩,
    ⟨[12, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      23, 7,
      1, 0⟩,
    ⟨[12, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      17, 7,
      1, 0⟩,
    ⟨[12, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 1,
      11, 7,
      1, 0⟩,
    ⟨[12, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 7,
      5, 7,
      1, 0⟩,
    ⟨[12, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 13,
      35, 7,
      1, 0⟩,
    ⟨[18, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 25,
      29, 7,
      1, 0⟩,
    ⟨[18, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard105 :
    z180K30ExceptionalLiteralWitnessesV87Shard105.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
