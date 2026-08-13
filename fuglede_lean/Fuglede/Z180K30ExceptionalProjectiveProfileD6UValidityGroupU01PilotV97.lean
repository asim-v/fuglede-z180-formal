import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C16PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C17PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C18PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU01C19PilotV97

/-! Structural aggregate for D6 U-profile class U01. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU01C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C09PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C10PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C11PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C12PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C13PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C14PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C15PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C16PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C17PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C18PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU01C19PilotV97)))))))))))))))))))

def z180K30ProjectiveD6UValidityClassU01PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU01PilotV97, members := z180K30ProjectiveD6UValidityMembersU01PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u01_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c08_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c09_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c10_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c11_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c12_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c13_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c14_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c15_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c16_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c17_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u01c18_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u01c19_forall_pilot_v97))))))))))))))))))))))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u01_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU01PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU01PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU01PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU01PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u01_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
