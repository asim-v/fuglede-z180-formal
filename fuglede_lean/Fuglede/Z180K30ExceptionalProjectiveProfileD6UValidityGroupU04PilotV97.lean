import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C16PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C17PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C18PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityLeafU04C19PilotV97

/-! Structural aggregate for D6 U-profile class U04. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04PilotV97 : List RawSet :=
  z180K30ProjectiveD6UValidityMembersU04C00PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C01PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C02PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C03PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C04PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C05PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C06PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C07PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C08PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C09PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C10PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C11PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C12PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C13PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C14PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C15PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C16PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C17PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C18PilotV97 ++ (z180K30ProjectiveD6UValidityMembersU04C19PilotV97)))))))))))))))))))

def z180K30ProjectiveD6UValidityClassU04PilotV97 : ProjectiveProfileClassV97 :=
  { profile := z180K30ProjectiveD6UValidityProfileU04PilotV97, members := z180K30ProjectiveD6UValidityMembersU04PilotV97 }

theorem z180_k30_projective_d6_u_validity_members_u04_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04PilotV97
  exact (List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c00_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c01_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c02_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c03_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c04_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c05_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c06_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c07_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c08_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c09_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c10_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c11_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c12_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c13_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c14_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c15_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c16_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c17_forall_pilot_v97 ((List.forall_append).2 (And.intro z180_k30_projective_d6_u_validity_members_u04c18_forall_pilot_v97 (z180_k30_projective_d6_u_validity_members_u04c19_forall_pilot_v97))))))))))))))))))))))))))))))))))))))

theorem z180_k30_projective_d6_u_validity_class_u04_valid_pilot_v97 :
    z180K30ProjectiveD6UValidityClassU04PilotV97.members.all
      (fun U => projectiveUProfileV97 6 U ==
        z180K30ProjectiveD6UValidityClassU04PilotV97.profile) = true := by
  change z180K30ProjectiveD6UValidityMembersU04PilotV97.all
    (fun U => projectiveUProfileV97 6 U == z180K30ProjectiveD6UValidityProfileU04PilotV97) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp z180_k30_projective_d6_u_validity_members_u04_forall_pilot_v97) U hU

end Fuglede.Z180K30ExceptionalRawV2
