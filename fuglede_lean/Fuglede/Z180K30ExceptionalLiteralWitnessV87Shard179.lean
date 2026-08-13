import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 179; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard179 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[27, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 11,
      16, 7,
      1, 0⟩,
    ⟨[27, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 17,
      10, 7,
      1, 0⟩,
    ⟨[33, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      0, 29,
      4, 7,
      1, 0⟩,
    ⟨[33, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      0, 35,
      34, 7,
      1, 0⟩,
    ⟨[33, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 5,
      28, 7,
      1, 0⟩,
    ⟨[33, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 11,
      22, 7,
      1, 0⟩,
    ⟨[33, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 17,
      16, 7,
      1, 0⟩,
    ⟨[33, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      0, 23,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard179 :
    z180K30ExceptionalLiteralWitnessesV87Shard179.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
