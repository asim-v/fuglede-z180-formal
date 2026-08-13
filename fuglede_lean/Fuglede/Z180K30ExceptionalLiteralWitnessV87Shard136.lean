import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 136; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard136 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 19, 31, 17], [0, 6, 12, 18, 24, 30],
      1, 7,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 23], [0, 6, 12, 18, 24, 30],
      5, 7,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 29], [0, 6, 12, 18, 24, 30],
      1, 1,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 35], [0, 6, 12, 18, 24, 30],
      5, 1,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 5], [0, 6, 12, 18, 24, 30],
      5, 13,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 11], [0, 6, 12, 18, 24, 30],
      1, 7,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 17], [0, 6, 12, 18, 24, 30],
      5, 7,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 23], [0, 6, 12, 18, 24, 30],
      1, 1,
      13, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard136 :
    z180K30ExceptionalLiteralWitnessesV87Shard136.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
