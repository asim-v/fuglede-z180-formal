import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicLeaf29PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicKeyDisjointRow30PilotV97

/-! Pairwise key-disjointness row 29; every decision compares two chunks of at most ten keys. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_key_disjoint_row_29_pilot_v97 :
    List.Pairwise List.Disjoint [z180K30ProjectiveD4ULeaf29KeysPilotV97,
    z180K30ProjectiveD4ULeaf30KeysPilotV97,
    z180K30ProjectiveD4ULeaf31KeysPilotV97] := by
  rw [List.pairwise_cons]
  constructor
  · intro values hvalues
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalues
    rcases hvalues with (rfl | rfl) <;>
      (rw [List.disjoint_left]; decide)
  · exact z180_k30_projective_d4_u_key_disjoint_row_30_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
