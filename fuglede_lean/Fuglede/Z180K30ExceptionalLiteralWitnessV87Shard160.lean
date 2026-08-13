import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 160; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard160 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[20, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 7,
      16, 7,
      1, 0⟩,
    ⟨[20, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 1,
      10, 7,
      1, 0⟩,
    ⟨[20, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 1,
      4, 7,
      1, 0⟩,
    ⟨[20, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 13,
      34, 7,
      1, 0⟩,
    ⟨[26, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      1, 7,
      28, 7,
      1, 0⟩,
    ⟨[26, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      5, 7,
      22, 7,
      1, 0⟩,
    ⟨[26, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 1,
      16, 7,
      1, 0⟩,
    ⟨[26, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 1,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard160 :
    z180K30ExceptionalLiteralWitnessesV87Shard160.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
