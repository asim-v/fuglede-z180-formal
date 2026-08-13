import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 92; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard92 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 24, 30, 28], [0, 6, 12, 18, 24, 30],
      5, 1,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 34], [0, 6, 12, 18, 24, 30],
      1, 13,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 4], [0, 6, 12, 18, 24, 30],
      1, 7,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 10], [0, 6, 12, 18, 24, 30],
      5, 7,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 16], [0, 6, 12, 18, 24, 30],
      1, 1,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 22], [0, 6, 12, 18, 24, 30],
      5, 1,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 28], [0, 6, 12, 18, 24, 30],
      1, 13,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 34], [0, 6, 12, 18, 24, 30],
      5, 13,
      6, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard92 :
    z180K30ExceptionalLiteralWitnessesV87Shard92.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
