import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 180; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard180 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 9, 15, 21, 27, 5], [0, 6, 12, 18, 24, 30],
      1, 11,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 11], [0, 6, 12, 18, 24, 30],
      5, 5,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 17], [0, 6, 12, 18, 24, 30],
      1, 5,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 23], [0, 6, 12, 18, 24, 30],
      5, 17,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 29], [0, 6, 12, 18, 24, 30],
      1, 17,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 35], [0, 6, 12, 18, 24, 30],
      5, 11,
      3, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 5], [0, 6, 12, 18, 24, 30],
      5, 5,
      33, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 11], [0, 6, 12, 18, 24, 30],
      1, 5,
      33, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard180 :
    z180K30ExceptionalLiteralWitnessesV87Shard180.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
