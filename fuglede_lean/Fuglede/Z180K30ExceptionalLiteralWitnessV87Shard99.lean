import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 99; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard99 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 18, 24, 5], [0, 6, 12, 18, 24, 30],
      0, 5,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 11], [0, 6, 12, 18, 24, 30],
      0, 11,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 17], [0, 6, 12, 18, 24, 30],
      0, 17,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 23], [0, 6, 12, 18, 24, 30],
      0, 23,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 29], [0, 6, 12, 18, 24, 30],
      0, 29,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 24, 35], [0, 6, 12, 18, 24, 30],
      0, 35,
      0, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 5], [0, 6, 12, 18, 24, 30],
      0, 11,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 11], [0, 6, 12, 18, 24, 30],
      0, 17,
      30, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard99 :
    z180K30ExceptionalLiteralWitnessesV87Shard99.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
