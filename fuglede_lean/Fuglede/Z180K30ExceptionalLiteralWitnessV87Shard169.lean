import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 169; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard169 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[20, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      17, 7,
      1, 0⟩,
    ⟨[20, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 5,
      23, 7,
      1, 0⟩,
    ⟨[20, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 1,
      5, 7,
      1, 0⟩,
    ⟨[20, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 1,
      35, 7,
      1, 0⟩,
    ⟨[26, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      3, 7,
      29, 7,
      1, 0⟩,
    ⟨[26, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      23, 7,
      1, 0⟩,
    ⟨[26, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 5,
      29, 7,
      1, 0⟩,
    ⟨[26, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 1,
      11, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard169 :
    z180K30ExceptionalLiteralWitnessesV87Shard169.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
