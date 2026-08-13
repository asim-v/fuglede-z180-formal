import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 189; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard189 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[4, 10, 16, 22, 28, 5], [0, 6, 12, 18, 24, 30],
      0, 13,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 28, 11], [0, 6, 12, 18, 24, 30],
      0, 19,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 28, 17], [0, 6, 12, 18, 24, 30],
      0, 25,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 28, 23], [0, 6, 12, 18, 24, 30],
      0, 31,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 28, 29], [0, 6, 12, 18, 24, 30],
      0, 1,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 28, 35], [0, 6, 12, 18, 24, 30],
      0, 7,
      28, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 34, 5], [0, 6, 12, 18, 24, 30],
      0, 19,
      22, 7,
      1, 0⟩,
    ⟨[4, 10, 16, 22, 34, 11], [0, 6, 12, 18, 24, 30],
      0, 25,
      22, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard189 :
    z180K30ExceptionalLiteralWitnessesV87Shard189.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
