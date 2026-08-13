import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 120; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard120 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 13, 19, 25, 31, 3], [0, 6, 12, 18, 24, 30],
      1, 17,
      13, 7,
      1, 0⟩,
    ⟨[1, 13, 19, 25, 31, 9], [0, 6, 12, 18, 24, 30],
      5, 11,
      13, 7,
      1, 0⟩,
    ⟨[1, 13, 19, 25, 31, 15], [0, 6, 12, 18, 24, 30],
      1, 11,
      13, 7,
      1, 0⟩,
    ⟨[1, 13, 19, 25, 31, 21], [0, 6, 12, 18, 24, 30],
      5, 5,
      13, 7,
      1, 0⟩,
    ⟨[1, 13, 19, 25, 31, 27], [0, 6, 12, 18, 24, 30],
      1, 5,
      13, 7,
      1, 0⟩,
    ⟨[1, 13, 19, 25, 31, 33], [0, 6, 12, 18, 24, 30],
      5, 17,
      13, 7,
      1, 0⟩,
    ⟨[1, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      1, 1,
      27, 7,
      1, 0⟩,
    ⟨[1, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      5, 1,
      21, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard120 :
    z180K30ExceptionalLiteralWitnessesV87Shard120.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
