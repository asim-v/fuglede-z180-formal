import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 93; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard93 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 12, 18, 24, 30, 4], [0, 6, 12, 18, 24, 30],
      5, 7,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 10], [0, 6, 12, 18, 24, 30],
      1, 1,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 16], [0, 6, 12, 18, 24, 30],
      5, 1,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 22], [0, 6, 12, 18, 24, 30],
      1, 13,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 28], [0, 6, 12, 18, 24, 30],
      5, 13,
      0, 7,
      1, 0⟩,
    ⟨[0, 12, 18, 24, 30, 34], [0, 6, 12, 18, 24, 30],
      1, 7,
      0, 7,
      1, 0⟩,
    ⟨[0, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      5, 11,
      4, 7,
      1, 0⟩,
    ⟨[0, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      1, 11,
      34, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard93 :
    z180K30ExceptionalLiteralWitnessesV87Shard93.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
