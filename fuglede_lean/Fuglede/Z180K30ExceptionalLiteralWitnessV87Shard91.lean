import Fuglede.Z180K30ExceptionalLiteralWitnessCoreV87

/-! Explicit affine-witness shard 91; no orbit search and no choose/drop. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalLiteralWitnessesV87Shard91 :
    List LiteralExceptionalPairWitnessV87 :=
  [
    ⟨[0, 6, 12, 18, 30, 16], [0, 6, 12, 18, 24, 30],
      1, 7,
      18, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 22], [0, 6, 12, 18, 24, 30],
      5, 7,
      18, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 28], [0, 6, 12, 18, 24, 30],
      1, 1,
      18, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 18, 30, 34], [0, 6, 12, 18, 24, 30],
      5, 1,
      18, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 4], [0, 6, 12, 18, 24, 30],
      5, 13,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 10], [0, 6, 12, 18, 24, 30],
      1, 7,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 16], [0, 6, 12, 18, 24, 30],
      5, 7,
      12, 7,
      1, 0⟩,
    ⟨[0, 6, 12, 24, 30, 22], [0, 6, 12, 18, 24, 30],
      1, 1,
      12, 7,
      1, 0⟩
  ]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_literal_witnesses_v87_shard91 :
    z180K30ExceptionalLiteralWitnessesV87Shard91.all
      literalExceptionalPairWitnessB_v87 = true := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
