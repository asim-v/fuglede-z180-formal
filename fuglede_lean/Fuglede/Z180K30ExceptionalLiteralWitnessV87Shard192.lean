import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 192; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard192 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[4, 16, 22, 28, 34, 5], [0, 6, 12, 18, 24, 30],
      0, 1,
      4, 7,
      1, 0⟩,
    ⟨[4, 16, 22, 28, 34, 11], [0, 6, 12, 18, 24, 30],
      0, 7,
      4, 7,
      1, 0⟩,
    ⟨[4, 16, 22, 28, 34, 17], [0, 6, 12, 18, 24, 30],
      0, 13,
      4, 7,
      1, 0⟩,
    ⟨[4, 16, 22, 28, 34, 23], [0, 6, 12, 18, 24, 30],
      0, 19,
      4, 7,
      1, 0⟩,
    ⟨[4, 16, 22, 28, 34, 29], [0, 6, 12, 18, 24, 30],
      0, 25,
      4, 7,
      1, 0⟩,
    ⟨[4, 16, 22, 28, 34, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      4, 7,
      1, 0⟩,
    ⟨[4, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 35,
      5, 7,
      1, 0⟩,
    ⟨[4, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 5,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard192 :
    z180K30ExceptionalLiteralWitnessesV87Shard192.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
