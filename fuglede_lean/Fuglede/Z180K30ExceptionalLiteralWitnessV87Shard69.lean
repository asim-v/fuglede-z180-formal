import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 69; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard69 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[12, 1, 7, 13, 19, 25], [0, 6, 12, 18, 24, 30],
      0, 11,
      1, 7,
      1, 0⟩,
    ⟨[12, 1, 7, 13, 19, 31], [0, 6, 12, 18, 24, 30],
      0, 17,
      31, 7,
      1, 0⟩,
    ⟨[12, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 23,
      25, 7,
      1, 0⟩,
    ⟨[12, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 29,
      19, 7,
      1, 0⟩,
    ⟨[12, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 35,
      13, 7,
      1, 0⟩,
    ⟨[12, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 5,
      7, 7,
      1, 0⟩,
    ⟨[18, 1, 7, 13, 19, 25], [0, 6, 12, 18, 24, 30],
      0, 17,
      1, 7,
      1, 0⟩,
    ⟨[18, 1, 7, 13, 19, 31], [0, 6, 12, 18, 24, 30],
      0, 23,
      31, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard69 :
    z180K30ExceptionalLiteralWitnessesV87Shard69.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
