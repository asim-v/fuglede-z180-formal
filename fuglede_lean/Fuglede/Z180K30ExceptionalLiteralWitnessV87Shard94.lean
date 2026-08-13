import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 94; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard94 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 5,
      28, 7,
      1, 0⟩,
    ⟨[0, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 5,
      22, 7,
      1, 0⟩,
    ⟨[0, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 17,
      16, 7,
      1, 0⟩,
    ⟨[0, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 17,
      10, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 4], [0, 6, 12, 18, 24, 30],
      1, 1,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 10], [0, 6, 12, 18, 24, 30],
      5, 1,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 16], [0, 6, 12, 18, 24, 30],
      1, 13,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 22], [0, 6, 12, 18, 24, 30],
      5, 13,
      30, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard94 :
    z180K30ExceptionalLiteralWitnessesV87Shard94.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
