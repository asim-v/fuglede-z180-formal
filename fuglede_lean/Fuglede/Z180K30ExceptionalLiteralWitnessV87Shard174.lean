import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 174; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard174 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 15, 21, 27, 33, 4], [0, 6, 12, 18, 24, 30],
      0, 1,
      3, 7,
      1, 0⟩,
    ⟨[3, 15, 21, 27, 33, 10], [0, 6, 12, 18, 24, 30],
      0, 7,
      3, 7,
      1, 0⟩,
    ⟨[3, 15, 21, 27, 33, 16], [0, 6, 12, 18, 24, 30],
      0, 13,
      3, 7,
      1, 0⟩,
    ⟨[3, 15, 21, 27, 33, 22], [0, 6, 12, 18, 24, 30],
      0, 19,
      3, 7,
      1, 0⟩,
    ⟨[3, 15, 21, 27, 33, 28], [0, 6, 12, 18, 24, 30],
      0, 25,
      3, 7,
      1, 0⟩,
    ⟨[3, 15, 21, 27, 33, 34], [0, 6, 12, 18, 24, 30],
      0, 31,
      3, 7,
      1, 0⟩,
    ⟨[3, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      0, 35,
      4, 7,
      1, 0⟩,
    ⟨[3, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      0, 5,
      34, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard174 :
    z180K30ExceptionalLiteralWitnessesV87Shard174.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
