import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 168; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard168 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[14, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      6, 1,
      29, 7,
      1, 0⟩,
    ⟨[14, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      6, 11,
      35, 7,
      1, 0⟩,
    ⟨[14, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 7,
      17, 7,
      1, 0⟩,
    ⟨[14, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 7,
      11, 7,
      1, 0⟩,
    ⟨[14, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      6, 5,
      17, 7,
      1, 0⟩,
    ⟨[14, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      3, 1,
      35, 7,
      1, 0⟩,
    ⟨[20, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      6, 11,
      5, 7,
      1, 0⟩,
    ⟨[20, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      3, 7,
      23, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard168 :
    z180K30ExceptionalLiteralWitnessesV87Shard168.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
