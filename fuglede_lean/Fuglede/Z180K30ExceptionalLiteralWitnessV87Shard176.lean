import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 176; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard176 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[9, 15, 21, 27, 33, 28], [0, 6, 12, 18, 24, 30],
      0, 31,
      33, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 34], [0, 6, 12, 18, 24, 30],
      0, 1,
      33, 7,
      1, 0⟩,
    ⟨[9, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      0, 5,
      4, 7,
      1, 0⟩,
    ⟨[9, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      0, 11,
      34, 7,
      1, 0⟩,
    ⟨[9, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 17,
      28, 7,
      1, 0⟩,
    ⟨[9, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 23,
      22, 7,
      1, 0⟩,
    ⟨[9, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 29,
      16, 7,
      1, 0⟩,
    ⟨[9, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 35,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard176 :
    z180K30ExceptionalLiteralWitnessesV87Shard176.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
