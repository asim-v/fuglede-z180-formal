import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 119; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard119 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 25, 31, 27], [0, 6, 12, 18, 24, 30],
      1, 11,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 25, 31, 33], [0, 6, 12, 18, 24, 30],
      5, 5,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 3], [0, 6, 12, 18, 24, 30],
      5, 17,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 9], [0, 6, 12, 18, 24, 30],
      1, 17,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 15], [0, 6, 12, 18, 24, 30],
      5, 11,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 21], [0, 6, 12, 18, 24, 30],
      1, 11,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 27], [0, 6, 12, 18, 24, 30],
      5, 5,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 19, 25, 31, 33], [0, 6, 12, 18, 24, 30],
      1, 5,
      19, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard119 :
    z180K30ExceptionalLiteralWitnessesV87Shard119.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
