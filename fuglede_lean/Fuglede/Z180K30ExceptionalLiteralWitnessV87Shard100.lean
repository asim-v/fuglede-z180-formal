import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 100; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard100 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 18, 30, 17], [0, 6, 12, 18, 24, 30],
      0, 23,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 23], [0, 6, 12, 18, 24, 30],
      0, 29,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 29], [0, 6, 12, 18, 24, 30],
      0, 35,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 35], [0, 6, 12, 18, 24, 30],
      0, 5,
      30, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 5], [0, 6, 12, 18, 24, 30],
      0, 17,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 11], [0, 6, 12, 18, 24, 30],
      0, 23,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 17], [0, 6, 12, 18, 24, 30],
      0, 29,
      24, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 23], [0, 6, 12, 18, 24, 30],
      0, 35,
      24, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard100 :
    z180K30ExceptionalLiteralWitnessesV87Shard100.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
