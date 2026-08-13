import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 133; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard133 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[19, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 7,
      16, 7,
      1, 0⟩,
    ⟨[19, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 5,
      22, 7,
      1, 0⟩,
    ⟨[19, 4, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      3, 1,
      4, 7,
      1, 0⟩,
    ⟨[19, 10, 16, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 1,
      34, 7,
      1, 0⟩,
    ⟨[25, 4, 10, 16, 22, 28], [0, 6, 12, 18, 24, 30],
      3, 7,
      28, 7,
      1, 0⟩,
    ⟨[25, 4, 10, 16, 22, 34], [0, 6, 12, 18, 24, 30],
      6, 7,
      22, 7,
      1, 0⟩,
    ⟨[25, 4, 10, 16, 28, 34], [0, 6, 12, 18, 24, 30],
      6, 5,
      28, 7,
      1, 0⟩,
    ⟨[25, 4, 10, 22, 28, 34], [0, 6, 12, 18, 24, 30],
      3, 1,
      10, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard133 :
    z180K30ExceptionalLiteralWitnessesV87Shard133.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
