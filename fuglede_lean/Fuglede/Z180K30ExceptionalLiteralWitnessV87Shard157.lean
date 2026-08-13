import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 157; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard157 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 13,
      16, 7,
      1, 0⟩,
    ⟨[2, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 13,
      10, 7,
      1, 0⟩,
    ⟨[2, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      1, 7,
      4, 7,
      1, 0⟩,
    ⟨[2, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      5, 7,
      34, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 4], [0, 6, 12, 18, 24, 30],
      5, 11,
      8, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 10], [0, 6, 12, 18, 24, 30],
      1, 11,
      8, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 16], [0, 6, 12, 18, 24, 30],
      5, 5,
      8, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 22], [0, 6, 12, 18, 24, 30],
      1, 5,
      8, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard157 :
    z180K30ExceptionalLiteralWitnessesV87Shard157.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
