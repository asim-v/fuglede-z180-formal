import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 172; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard172 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[3, 9, 15, 21, 33, 16], [0, 6, 12, 18, 24, 30],
      0, 31,
      21, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 22], [0, 6, 12, 18, 24, 30],
      0, 1,
      21, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 28], [0, 6, 12, 18, 24, 30],
      0, 7,
      21, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 21, 33, 34], [0, 6, 12, 18, 24, 30],
      0, 13,
      21, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 4], [0, 6, 12, 18, 24, 30],
      0, 25,
      15, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 10], [0, 6, 12, 18, 24, 30],
      0, 31,
      15, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 16], [0, 6, 12, 18, 24, 30],
      0, 1,
      15, 7,
      1, 0⟩,
    ⟨[3, 9, 15, 27, 33, 22], [0, 6, 12, 18, 24, 30],
      0, 7,
      15, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard172 :
    z180K30ExceptionalLiteralWitnessesV87Shard172.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
