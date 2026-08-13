import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU07C09PilotV97

/-! Structural aggregate for D6 U-profile class U07. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU07C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU07C09PilotV97)))))))))

def z180K30ProjectiveD6UValidityClassU07PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU07PilotV97, members := z180K30ProjectiveD6UValidityMembersU07PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u07_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u07c08_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u07c09_forall_pilot_v97))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u07_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU07PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU07PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU07PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU07PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u07_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
