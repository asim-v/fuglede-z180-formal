import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 70; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard70 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[18, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 29,
      25, 7,
      1, 0⟩,
    ⟨[18, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 35,
      19, 7,
      1, 0⟩,
    ⟨[18, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 5,
      13, 7,
      1, 0⟩,
    ⟨[18, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 11,
      7, 7,
      1, 0⟩,
    ⟨[24, 1, 7, 13, 19, 25], [0, 6, 12, 18, 24, 30],
      0, 23,
      1, 7,
      1, 0⟩,
    ⟨[24, 1, 7, 13, 19, 31], [0, 6, 12, 18, 24, 30],
      0, 29,
      31, 7,
      1, 0⟩,
    ⟨[24, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 35,
      25, 7,
      1, 0⟩,
    ⟨[24, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 5,
      19, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard70 :
    z180K30ExceptionalLiteralWitnessesV87Shard70.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
