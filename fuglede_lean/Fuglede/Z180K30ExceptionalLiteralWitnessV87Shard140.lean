import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 140; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard140 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[7, 13, 19, 25, 31, 29], [0, 6, 12, 18, 24, 30],
      1, 7,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 35], [0, 6, 12, 18, 24, 30],
      5, 7,
      31, 7,
      1, 0⟩,
    ⟨[7, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      1, 11,
      5, 7,
      1, 0⟩,
    ⟨[7, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      5, 5,
      35, 7,
      1, 0⟩,
    ⟨[7, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 5,
      29, 7,
      1, 0⟩,
    ⟨[7, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 17,
      23, 7,
      1, 0⟩,
    ⟨[7, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 17,
      17, 7,
      1, 0⟩,
    ⟨[7, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 11,
      11, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard140 :
    z180K30ExceptionalLiteralWitnessesV87Shard140.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
