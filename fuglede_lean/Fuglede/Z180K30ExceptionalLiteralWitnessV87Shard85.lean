import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 85; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard85 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 1,
      15, 7,
      1, 0⟩,
    ⟨[0, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      21, 7,
      1, 0⟩,
    ⟨[0, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 7,
      3, 7,
      1, 0⟩,
    ⟨[0, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 7,
      33, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 3], [0, 6, 12, 18, 24, 30],
      6, 5,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 9], [0, 6, 12, 18, 24, 30],
      3, 1,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 15], [0, 6, 12, 18, 24, 30],
      6, 1,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 21], [0, 6, 12, 18, 24, 30],
      6, 11,
      6, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard85 :
    z180K30ExceptionalLiteralWitnessesV87Shard85.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
