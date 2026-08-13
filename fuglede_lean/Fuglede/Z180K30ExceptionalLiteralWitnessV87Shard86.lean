import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 86; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard86 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[6, 12, 18, 24, 30, 27], [0, 6, 12, 18, 24, 30],
      3, 7,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 33], [0, 6, 12, 18, 24, 30],
      6, 7,
      30, 7,
      1, 0⟩,
    ⟨[6, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      3, 1,
      27, 7,
      1, 0⟩,
    ⟨[6, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      6, 1,
      21, 7,
      1, 0⟩,
    ⟨[6, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      27, 7,
      1, 0⟩,
    ⟨[6, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 7,
      9, 7,
      1, 0⟩,
    ⟨[6, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 7,
      3, 7,
      1, 0⟩,
    ⟨[6, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 5,
      9, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard86 :
    z180K30ExceptionalLiteralWitnessesV87Shard86.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
