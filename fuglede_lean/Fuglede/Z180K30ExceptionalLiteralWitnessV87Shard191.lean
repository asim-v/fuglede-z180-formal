import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 191; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard191 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[4, 10, 16, 28, 34, 29], [0, 6, 12, 18, 24, 30],
      0, 13,
      16, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 28, 34, 35], [0, 6, 12, 18, 24, 30],
      0, 19,
      16, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 5], [0, 6, 12, 18, 24, 30],
      0, 31,
      10, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 11], [0, 6, 12, 18, 24, 30],
      0, 1,
      10, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 17], [0, 6, 12, 18, 24, 30],
      0, 7,
      10, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 23], [0, 6, 12, 18, 24, 30],
      0, 13,
      10, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 29], [0, 6, 12, 18, 24, 30],
      0, 19,
      10, 7,
      1, 0⟩,
    ⟨[4, 10, 22, 28, 34, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard191 :
    z180K30ExceptionalLiteralWitnessesV87Shard191.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
