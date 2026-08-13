import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 184; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard184 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 13,
      17, 7,
      1, 0⟩,
    ⟨[3, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 13,
      11, 7,
      1, 0⟩,
    ⟨[3, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 7,
      5, 7,
      1, 0⟩,
    ⟨[3, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 7,
      35, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 5], [0, 6, 12, 18, 24, 30],
      5, 11,
      9, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 11], [0, 6, 12, 18, 24, 30],
      1, 11,
      9, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 17], [0, 6, 12, 18, 24, 30],
      5, 5,
      9, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 23], [0, 6, 12, 18, 24, 30],
      1, 5,
      9, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard184 :
    z180K30ExceptionalLiteralWitnessesV87Shard184.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
