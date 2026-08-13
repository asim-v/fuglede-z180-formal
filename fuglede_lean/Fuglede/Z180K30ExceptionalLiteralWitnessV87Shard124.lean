import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 124; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard124 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[19, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      5, 7,
      15, 7,
      1, 0⟩,
    ⟨[19, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      1, 1,
      9, 7,
      1, 0⟩,
    ⟨[19, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      5, 1,
      3, 7,
      1, 0⟩,
    ⟨[19, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      1, 13,
      33, 7,
      1, 0⟩,
    ⟨[25, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      1, 7,
      27, 7,
      1, 0⟩,
    ⟨[25, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      5, 7,
      21, 7,
      1, 0⟩,
    ⟨[25, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      1, 1,
      15, 7,
      1, 0⟩,
    ⟨[25, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      5, 1,
      9, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard124 :
    z180K30ExceptionalLiteralWitnessesV87Shard124.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
