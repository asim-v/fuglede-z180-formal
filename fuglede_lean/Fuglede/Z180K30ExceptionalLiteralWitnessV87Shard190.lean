import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 190; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard190 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[4, 10, 16, 22, 34, 17], [0, 6, 12, 18, 24, 30],
      0, 31,
      22, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 34, 23], [0, 6, 12, 18, 24, 30],
      0, 1,
      22, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 34, 29], [0, 6, 12, 18, 24, 30],
      0, 7,
      22, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 34, 35], [0, 6, 12, 18, 24, 30],
      0, 13,
      22, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 28, 34, 5], [0, 6, 12, 18, 24, 30],
      0, 25,
      16, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 28, 34, 11], [0, 6, 12, 18, 24, 30],
      0, 31,
      16, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 28, 34, 17], [0, 6, 12, 18, 24, 30],
      0, 1,
      16, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 28, 34, 23], [0, 6, 12, 18, 24, 30],
      0, 7,
      16, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard190 :
    z180K30ExceptionalLiteralWitnessesV87Shard190.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
