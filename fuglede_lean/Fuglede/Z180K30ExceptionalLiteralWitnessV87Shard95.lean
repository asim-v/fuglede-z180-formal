import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 95; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard95 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[6, 12, 18, 24, 30, 28], [0, 6, 12, 18, 24, 30],
      1, 7,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 34], [0, 6, 12, 18, 24, 30],
      5, 7,
      30, 7,
      1, 0⟩,
    ⟨[6, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      1, 11,
      4, 7,
      1, 0⟩,
    ⟨[6, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      5, 5,
      34, 7,
      1, 0⟩,
    ⟨[6, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 5,
      28, 7,
      1, 0⟩,
    ⟨[6, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 17,
      22, 7,
      1, 0⟩,
    ⟨[6, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 17,
      16, 7,
      1, 0⟩,
    ⟨[6, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 11,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard95 :
    z180K30ExceptionalLiteralWitnessesV87Shard95.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
