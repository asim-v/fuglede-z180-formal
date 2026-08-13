import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 162; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard162 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[2, 8, 14, 20, 26, 5], [0, 6, 12, 18, 24, 30],
      3, 1,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 11], [0, 6, 12, 18, 24, 30],
      6, 1,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 17], [0, 6, 12, 18, 24, 30],
      6, 11,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 23], [0, 6, 12, 18, 24, 30],
      3, 7,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 29], [0, 6, 12, 18, 24, 30],
      6, 7,
      26, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 26, 35], [0, 6, 12, 18, 24, 30],
      6, 5,
      2, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 5], [0, 6, 12, 18, 24, 30],
      6, 1,
      20, 7,
      1, 0⟩,
    ⟨[2, 8, 14, 20, 32, 11], [0, 6, 12, 18, 24, 30],
      6, 11,
      32, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard162 :
    z180K30ExceptionalLiteralWitnessesV87Shard162.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
