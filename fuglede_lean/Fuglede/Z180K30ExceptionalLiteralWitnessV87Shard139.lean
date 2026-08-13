import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 139; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard139 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 5,
      29, 7,
      1, 0⟩,
    ⟨[1, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 5,
      23, 7,
      1, 0⟩,
    ⟨[1, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 17,
      17, 7,
      1, 0⟩,
    ⟨[1, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 17,
      11, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 5], [0, 6, 12, 18, 24, 30],
      1, 1,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 11], [0, 6, 12, 18, 24, 30],
      5, 1,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 17], [0, 6, 12, 18, 24, 30],
      1, 13,
      31, 7,
      1, 0⟩,
    ⟨[7, 13, 19, 25, 31, 23], [0, 6, 12, 18, 24, 30],
      5, 13,
      31, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard139 :
    z180K30ExceptionalLiteralWitnessesV87Shard139.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
