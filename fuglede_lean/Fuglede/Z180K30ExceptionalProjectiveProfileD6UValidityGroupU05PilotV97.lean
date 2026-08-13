import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C16PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C17PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C18PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C19PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C20PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C21PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU05C22PilotV97

/-! Structural aggregate for D6 U-profile class U05. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU05C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C09PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C10PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C11PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C12PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C13PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C14PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C15PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C16PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C17PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C18PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C19PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C20PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C21PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU05C22PilotV97))))))))))))))))))))))

def z180K30ProjectiveD6UValidityClassU05PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU05PilotV97, members := z180K30ProjectiveD6UValidityMembersU05PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u05_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c08_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c09_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c10_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c11_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c12_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c13_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c14_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c15_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c16_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c17_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c18_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c19_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c20_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u05c21_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u05c22_forall_pilot_v97))))))))))))))))))))))))))))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u05_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU05PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU05PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU05PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU05PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u05_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
