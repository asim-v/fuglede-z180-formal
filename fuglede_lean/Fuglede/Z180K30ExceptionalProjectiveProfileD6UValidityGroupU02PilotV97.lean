import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C16PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C17PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C18PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C19PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C20PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C21PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU02C22PilotV97

/-! Structural aggregate for D6 U-profile class U02. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU02C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C09PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C10PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C11PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C12PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C13PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C14PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C15PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C16PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C17PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C18PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C19PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C20PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C21PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU02C22PilotV97))))))))))))))))))))))

def z180K30ProjectiveD6UValidityClassU02PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU02PilotV97, members := z180K30ProjectiveD6UValidityMembersU02PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u02_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c08_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c09_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c10_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c11_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c12_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c13_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c14_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c15_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c16_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c17_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c18_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c19_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c20_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u02c21_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u02c22_forall_pilot_v97))))))))))))))))))))))))))))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u02_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU02PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU02PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU02PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU02PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u02_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
