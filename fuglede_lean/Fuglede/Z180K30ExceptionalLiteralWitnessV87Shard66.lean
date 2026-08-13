import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 66; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard66 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 12, 18, 24, 30, 1], [0, 6, 12, 18, 24, 30],
      0, 1,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 7], [0, 6, 12, 18, 24, 30],
      0, 7,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 13], [0, 6, 12, 18, 24, 30],
      0, 13,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 19], [0, 6, 12, 18, 24, 30],
      0, 19,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 25], [0, 6, 12, 18, 24, 30],
      0, 25,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 31], [0, 6, 12, 18, 24, 30],
      0, 31,
      0, 7,
      1, 0⟩,
    ⟨[0, 1, 7, 13, 19, 25], [0, 6, 12, 18, 24, 30],
      0, 35,
      1, 7,
      1, 0⟩,
    ⟨[0, 1, 7, 13, 19, 31], [0, 6, 12, 18, 24, 30],
      0, 5,
      31, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard66 :
    z180K30ExceptionalLiteralWitnessesV87Shard66.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
