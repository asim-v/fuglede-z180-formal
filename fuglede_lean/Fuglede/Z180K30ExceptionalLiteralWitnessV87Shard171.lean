import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 171; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard171 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 9, 15, 21, 27, 4], [0, 6, 12, 18, 24, 30],
      0, 13,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 10], [0, 6, 12, 18, 24, 30],
      0, 19,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 16], [0, 6, 12, 18, 24, 30],
      0, 25,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 22], [0, 6, 12, 18, 24, 30],
      0, 31,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 28], [0, 6, 12, 18, 24, 30],
      0, 1,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 27, 34], [0, 6, 12, 18, 24, 30],
      0, 7,
      27, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 4], [0, 6, 12, 18, 24, 30],
      0, 19,
      21, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 10], [0, 6, 12, 18, 24, 30],
      0, 25,
      21, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard171 :
    z180K30ExceptionalLiteralWitnessesV87Shard171.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
