import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 67; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard67 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 1, 7, 13, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 11,
      25, 7,
      1, 0⟩,
    ⟨[0, 1, 7, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 17,
      19, 7,
      1, 0⟩,
    ⟨[0, 1, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 23,
      13, 7,
      1, 0⟩,
    ⟨[0, 7, 13, 19, 25, 31], [0, 6, 12, 18, 24, 30],
      0, 29,
      7, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 1], [0, 6, 12, 18, 24, 30],
      0, 7,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 7], [0, 6, 12, 18, 24, 30],
      0, 13,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 13], [0, 6, 12, 18, 24, 30],
      0, 19,
      30, 7,
      1, 0⟩,
    ⟨[6, 12, 18, 24, 30, 19], [0, 6, 12, 18, 24, 30],
      0, 25,
      30, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard67 :
    z180K30ExceptionalLiteralWitnessesV87Shard67.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
