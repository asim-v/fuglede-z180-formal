import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 89; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard89 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[24, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 1,
      3, 7,
      1, 0⟩,
    ⟨[24, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      9, 7,
      1, 0⟩,
    ⟨[30, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      6, 7,
      27, 7,
      1, 0⟩,
    ⟨[30, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      6, 5,
      33, 7,
      1, 0⟩,
    ⟨[30, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 1,
      15, 7,
      1, 0⟩,
    ⟨[30, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 1,
      9, 7,
      1, 0⟩,
    ⟨[30, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      15, 7,
      1, 0⟩,
    ⟨[30, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 7,
      33, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard89 :
    z180K30ExceptionalLiteralWitnessesV87Shard89.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
