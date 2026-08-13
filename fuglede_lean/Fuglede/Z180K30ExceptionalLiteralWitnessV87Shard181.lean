import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 181; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard181 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 9, 15, 21, 33, 17], [0, 6, 12, 18, 24, 30],
      5, 17,
      33, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 23], [0, 6, 12, 18, 24, 30],
      1, 17,
      33, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 29], [0, 6, 12, 18, 24, 30],
      5, 11,
      33, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 35], [0, 6, 12, 18, 24, 30],
      1, 11,
      33, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 5], [0, 6, 12, 18, 24, 30],
      1, 5,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 11], [0, 6, 12, 18, 24, 30],
      5, 17,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 17], [0, 6, 12, 18, 24, 30],
      1, 17,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 23], [0, 6, 12, 18, 24, 30],
      5, 11,
      27, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard181 :
    z180K30ExceptionalLiteralWitnessesV87Shard181.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
