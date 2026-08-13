import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 121; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard121 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      1, 13,
      15, 7,
      1, 0⟩,
    ⟨[1, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      5, 13,
      9, 7,
      1, 0⟩,
    ⟨[1, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      1, 7,
      3, 7,
      1, 0⟩,
    ⟨[1, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      5, 7,
      33, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 3], [0, 6, 12, 18, 24, 30],
      5, 11,
      7, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 9], [0, 6, 12, 18, 24, 30],
      1, 11,
      7, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 15], [0, 6, 12, 18, 24, 30],
      5, 5,
      7, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 21], [0, 6, 12, 18, 24, 30],
      1, 5,
      7, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard121 :
    z180K30ExceptionalLiteralWitnessesV87Shard121.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
