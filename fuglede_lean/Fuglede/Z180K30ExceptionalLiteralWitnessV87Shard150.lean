import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 150; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard150 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[14, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      0, 11,
      3, 7,
      1, 0⟩,
    ⟨[14, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      0, 17,
      33, 7,
      1, 0⟩,
    ⟨[14, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 23,
      27, 7,
      1, 0⟩,
    ⟨[14, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 29,
      21, 7,
      1, 0⟩,
    ⟨[14, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 35,
      15, 7,
      1, 0⟩,
    ⟨[14, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 5,
      9, 7,
      1, 0⟩,
    ⟨[20, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      0, 17,
      3, 7,
      1, 0⟩,
    ⟨[20, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      0, 23,
      33, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard150 :
    z180K30ExceptionalLiteralWitnessesV87Shard150.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
