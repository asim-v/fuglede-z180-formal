import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 175; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard175 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 11,
      28, 7,
      1, 0⟩,
    ⟨[3, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 17,
      22, 7,
      1, 0⟩,
    ⟨[3, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 23,
      16, 7,
      1, 0⟩,
    ⟨[3, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 29,
      10, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 4], [0, 6, 12, 18, 24, 30],
      0, 7,
      33, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 10], [0, 6, 12, 18, 24, 30],
      0, 13,
      33, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 16], [0, 6, 12, 18, 24, 30],
      0, 19,
      33, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 22], [0, 6, 12, 18, 24, 30],
      0, 25,
      33, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard175 :
    z180K30ExceptionalLiteralWitnessesV87Shard175.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
