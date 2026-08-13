import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 130; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard130 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 1,
      16, 7,
      1, 0⟩,
    ⟨[1, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 11,
      22, 7,
      1, 0⟩,
    ⟨[1, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      3, 7,
      4, 7,
      1, 0⟩,
    ⟨[1, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 7,
      34, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 4], [0, 6, 12, 18, 24, 30],
      6, 5,
      7, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 10], [0, 6, 12, 18, 24, 30],
      3, 1,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 16], [0, 6, 12, 18, 24, 30],
      6, 1,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 22], [0, 6, 12, 18, 24, 30],
      6, 11,
      7, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard130 :
    z180K30ExceptionalLiteralWitnessesV87Shard130.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
