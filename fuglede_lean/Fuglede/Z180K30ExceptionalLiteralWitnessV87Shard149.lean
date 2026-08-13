import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 149; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard149 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[8, 14, 20, 26, 32, 27], [0, 6, 12, 18, 24, 30],
      0, 31,
      32, 7,
      1, 0⟩,
    ⟨[8, 14, 20, 26, 32, 33], [0, 6, 12, 18, 24, 30],
      0, 1,
      32, 7,
      1, 0⟩,
    ⟨[8, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      0, 5,
      3, 7,
      1, 0⟩,
    ⟨[8, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      0, 11,
      33, 7,
      1, 0⟩,
    ⟨[8, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 17,
      27, 7,
      1, 0⟩,
    ⟨[8, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 23,
      21, 7,
      1, 0⟩,
    ⟨[8, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 29,
      15, 7,
      1, 0⟩,
    ⟨[8, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      0, 35,
      9, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard149 :
    z180K30ExceptionalLiteralWitnessesV87Shard149.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
