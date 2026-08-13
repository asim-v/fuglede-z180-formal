import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 156; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard156 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 14, 20, 26, 32, 4], [0, 6, 12, 18, 24, 30],
      1, 17,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 10], [0, 6, 12, 18, 24, 30],
      5, 11,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 16], [0, 6, 12, 18, 24, 30],
      1, 11,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 22], [0, 6, 12, 18, 24, 30],
      5, 5,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 28], [0, 6, 12, 18, 24, 30],
      1, 5,
      14, 7,
      1, 0⟩,
    ⟨[2, 14, 20, 26, 32, 34], [0, 6, 12, 18, 24, 30],
      5, 17,
      14, 7,
      1, 0⟩,
    ⟨[2, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      1, 1,
      28, 7,
      1, 0⟩,
    ⟨[2, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      5, 1,
      22, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard156 :
    z180K30ExceptionalLiteralWitnessesV87Shard156.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
