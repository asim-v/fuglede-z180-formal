import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 152; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard152 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[26, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 11,
      15, 7,
      1, 0⟩,
    ⟨[26, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 17,
      9, 7,
      1, 0⟩,
    ⟨[32, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      0, 29,
      3, 7,
      1, 0⟩,
    ⟨[32, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      0, 35,
      33, 7,
      1, 0⟩,
    ⟨[32, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 5,
      27, 7,
      1, 0⟩,
    ⟨[32, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 11,
      21, 7,
      1, 0⟩,
    ⟨[32, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 17,
      15, 7,
      1, 0⟩,
    ⟨[32, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 23,
      9, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard152 :
    z180K30ExceptionalLiteralWitnessesV87Shard152.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
