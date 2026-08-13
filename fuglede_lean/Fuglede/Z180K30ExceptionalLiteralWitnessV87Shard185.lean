import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 185; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard185 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[9, 15, 21, 27, 33, 29], [0, 6, 12, 18, 24, 30],
      5, 17,
      9, 7,
      1, 0⟩,
    ⟨[9, 15, 21, 27, 33, 35], [0, 6, 12, 18, 24, 30],
      1, 17,
      9, 7,
      1, 0⟩,
    ⟨[9, 5, 11, 17, 23, 29], [0, 6, 12, 18, 24, 30],
      5, 1,
      29, 7,
      1, 0⟩,
    ⟨[9, 5, 11, 17, 23, 35], [0, 6, 12, 18, 24, 30],
      1, 13,
      23, 7,
      1, 0⟩,
    ⟨[9, 5, 11, 17, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 13,
      17, 7,
      1, 0⟩,
    ⟨[9, 5, 11, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 7,
      11, 7,
      1, 0⟩,
    ⟨[9, 5, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      5, 7,
      5, 7,
      1, 0⟩,
    ⟨[9, 11, 17, 23, 29, 35], [0, 6, 12, 18, 24, 30],
      1, 1,
      35, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard185 :
    z180K30ExceptionalLiteralWitnessesV87Shard185.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
