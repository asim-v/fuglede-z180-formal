import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 126; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard126 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[1, 7, 13, 19, 25, 4], [0, 6, 12, 18, 24, 30],
      3, 1,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 10], [0, 6, 12, 18, 24, 30],
      6, 1,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 16], [0, 6, 12, 18, 24, 30],
      6, 11,
      1, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 22], [0, 6, 12, 18, 24, 30],
      3, 7,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 28], [0, 6, 12, 18, 24, 30],
      6, 7,
      25, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 25, 34], [0, 6, 12, 18, 24, 30],
      6, 5,
      1, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 4], [0, 6, 12, 18, 24, 30],
      6, 1,
      19, 7,
      1, 0⟩,
    ⟨[1, 7, 13, 19, 31, 10], [0, 6, 12, 18, 24, 30],
      6, 11,
      31, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard126 :
    z180K30ExceptionalLiteralWitnessesV87Shard126.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
