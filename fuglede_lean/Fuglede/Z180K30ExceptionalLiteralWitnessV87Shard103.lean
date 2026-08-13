import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 103; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard103 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 19,
      17, 7,
      1, 0⟩,
    ⟨[0, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 25,
      11, 7,
      1, 0⟩,
    ⟨[0, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 31,
      5, 7,
      1, 0⟩,
    ⟨[0, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 1,
      35, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 5], [0, 6, 12, 18, 24, 30],
      0, 35,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 11], [0, 6, 12, 18, 24, 30],
      0, 5,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 17], [0, 6, 12, 18, 24, 30],
      0, 11,
      6, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 23], [0, 6, 12, 18, 24, 30],
      0, 17,
      6, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard103 :
    z180K30ExceptionalLiteralWitnessesV87Shard103.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
