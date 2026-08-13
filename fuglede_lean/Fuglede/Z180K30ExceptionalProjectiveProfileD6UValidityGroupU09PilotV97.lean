import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU09C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU09C01PilotV97

/-! Structural aggregate for D6 U-profile class U09. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU09PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU09C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU09C01PilotV97)

def z180K30ProjectiveD6UValidityClassU09PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU09PilotV97, members := z180K30ProjectiveD6UValidityMembersU09PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u09_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU09PilotV97)
      z180K30ProjectiveD6UValidityMembersU09PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU09PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u09c00_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u09c01_forall_pilot_v97))

theorem z180_k30_projective_d6_u_validity_class_u09_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU09PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU09PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU09PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU09PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u09_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
