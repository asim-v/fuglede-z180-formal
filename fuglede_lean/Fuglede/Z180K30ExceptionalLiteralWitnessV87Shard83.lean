import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 83; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard83 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 24, 30, 27], [0, 6, 12, 18, 24, 30],
      3, 1,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 33], [0, 6, 12, 18, 24, 30],
      6, 1,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 3], [0, 6, 12, 18, 24, 30],
      3, 7,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 9], [0, 6, 12, 18, 24, 30],
      6, 7,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 15], [0, 6, 12, 18, 24, 30],
      6, 5,
      18, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 21], [0, 6, 12, 18, 24, 30],
      3, 1,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 27], [0, 6, 12, 18, 24, 30],
      6, 1,
      6, 7,
      1, 0⟩,
    ⟨[0, 6, 18, 24, 30, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      18, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard83 :
    z180K30ExceptionalLiteralWitnessesV87Shard83.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
