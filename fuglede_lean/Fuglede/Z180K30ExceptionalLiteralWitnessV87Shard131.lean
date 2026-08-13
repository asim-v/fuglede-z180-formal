import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 131; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard131 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[7, 13, 19, 25, 31, 28], [0, 6, 12, 18, 24, 30],
      3, 7,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 34], [0, 6, 12, 18, 24, 30],
      6, 7,
      31, 7,
      1, 0⟩,
    ⟨[7, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      3, 1,
      28, 7,
      1, 0⟩,
    ⟨[7, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      6, 1,
      22, 7,
      1, 0⟩,
    ⟨[7, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 11,
      28, 7,
      1, 0⟩,
    ⟨[7, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      3, 7,
      10, 7,
      1, 0⟩,
    ⟨[7, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 7,
      4, 7,
      1, 0⟩,
    ⟨[7, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 5,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard131 :
    z180K30ExceptionalLiteralWitnessesV87Shard131.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
