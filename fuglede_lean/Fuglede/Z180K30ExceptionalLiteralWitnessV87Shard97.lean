import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 97; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard97 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[18, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 17,
      28, 7,
      1, 0⟩,
    ⟨[18, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 11,
      22, 7,
      1, 0⟩,
    ⟨[18, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 11,
      16, 7,
      1, 0⟩,
    ⟨[18, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 5,
      10, 7,
      1, 0⟩,
    ⟨[24, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      5, 17,
      4, 7,
      1, 0⟩,
    ⟨[24, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      1, 17,
      34, 7,
      1, 0⟩,
    ⟨[24, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 11,
      28, 7,
      1, 0⟩,
    ⟨[24, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 11,
      22, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard97 :
    z180K30ExceptionalLiteralWitnessesV87Shard97.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
