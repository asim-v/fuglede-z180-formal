import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 87; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard87 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[12, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      6, 1,
      27, 7,
      1, 0⟩,
    ⟨[12, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      6, 11,
      33, 7,
      1, 0⟩,
    ⟨[12, 3, 9, 15, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 7,
      15, 7,
      1, 0⟩,
    ⟨[12, 3, 9, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 7,
      9, 7,
      1, 0⟩,
    ⟨[12, 3, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      6, 5,
      15, 7,
      1, 0⟩,
    ⟨[12, 9, 15, 21, 27, 33], [0, 6, 12, 18, 24, 30],
      3, 1,
      33, 7,
      1, 0⟩,
    ⟨[18, 3, 9, 15, 21, 27], [0, 6, 12, 18, 24, 30],
      6, 11,
      3, 7,
      1, 0⟩,
    ⟨[18, 3, 9, 15, 21, 33], [0, 6, 12, 18, 24, 30],
      3, 7,
      21, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard87 :
    z180K30ExceptionalLiteralWitnessesV87Shard87.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
