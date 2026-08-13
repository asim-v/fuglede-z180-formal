import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 128; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard128 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 25, 31, 28], [0, 6, 12, 18, 24, 30],
      3, 1,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 34], [0, 6, 12, 18, 24, 30],
      6, 1,
      13, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 4], [0, 6, 12, 18, 24, 30],
      3, 7,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 10], [0, 6, 12, 18, 24, 30],
      6, 7,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 16], [0, 6, 12, 18, 24, 30],
      6, 5,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 22], [0, 6, 12, 18, 24, 30],
      3, 1,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 28], [0, 6, 12, 18, 24, 30],
      6, 1,
      7, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 34], [0, 6, 12, 18, 24, 30],
      6, 11,
      19, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard128 :
    z180K30ExceptionalLiteralWitnessesV87Shard128.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
