import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicLeaf15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicKeyDisjointRow16PilotV97

/-! Pairwise key-disjointness row 15; every decision compares two chunks of at most ten keys. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_key_disjoint_row_15_pilot_v97 :
    List.Pairwise List.Disjoint [z180K30ProjectiveD4ULeaf15KeysPilotV97,
    z180K30ProjectiveD4ULeaf16KeysPilotV97,
    z180K30ProjectiveD4ULeaf17KeysPilotV97,
    z180K30ProjectiveD4ULeaf18KeysPilotV97,
    z180K30ProjectiveD4ULeaf19KeysPilotV97,
    z180K30ProjectiveD4ULeaf20KeysPilotV97,
    z180K30ProjectiveD4ULeaf21KeysPilotV97,
    z180K30ProjectiveD4ULeaf22KeysPilotV97,
    z180K30ProjectiveD4ULeaf23KeysPilotV97,
    z180K30ProjectiveD4ULeaf24KeysPilotV97,
    z180K30ProjectiveD4ULeaf25KeysPilotV97,
    z180K30ProjectiveD4ULeaf26KeysPilotV97,
    z180K30ProjectiveD4ULeaf27KeysPilotV97,
    z180K30ProjectiveD4ULeaf28KeysPilotV97,
    z180K30ProjectiveD4ULeaf29KeysPilotV97,
    z180K30ProjectiveD4ULeaf30KeysPilotV97,
    z180K30ProjectiveD4ULeaf31KeysPilotV97] := by
  rw [List.pairwise_cons]
  constructor
  · intro values hvalues
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalues
    rcases hvalues with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (rw [List.disjoint_left]; decide)
  · exact z180_k30_projective_d4_u_key_disjoint_row_16_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
