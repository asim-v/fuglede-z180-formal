import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 195; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard195 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[16, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 11,
      5, 7,
      1, 0⟩,
    ⟨[16, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 17,
      35, 7,
      1, 0⟩,
    ⟨[16, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 23,
      29, 7,
      1, 0⟩,
    ⟨[16, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 29,
      23, 7,
      1, 0⟩,
    ⟨[16, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 35,
      17, 7,
      1, 0⟩,
    ⟨[16, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      0, 5,
      11, 7,
      1, 0⟩,
    ⟨[22, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      0, 17,
      5, 7,
      1, 0⟩,
    ⟨[22, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      0, 23,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard195 :
    z180K30ExceptionalLiteralWitnessesV87Shard195.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
