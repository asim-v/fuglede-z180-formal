import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU08C11PilotV97

/-! Structural aggregate for D6 U-profile class U08. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU08PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU08C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C09PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C10PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU08C11PilotV97)))))))))))

def z180K30ProjectiveD6UValidityClassU08PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU08PilotV97, members := z180K30ProjectiveD6UValidityMembersU08PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u08_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU08PilotV97)
      z180K30ProjectiveD6UValidityMembersU08PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU08PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c08_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c09_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u08c10_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u08c11_forall_pilot_v97))))))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u08_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU08PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU08PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU08PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU08PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u08_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
