import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S014
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S015

/-! Bounded D6 U-validity leaf U01C14: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C14PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0280, z180K30ProfileV97D6U01M0281, z180K30ProfileV97D6U01M0282, z180K30ProfileV97D6U01M0283, z180K30ProfileV97D6U01M0284, z180K30ProfileV97D6U01M0285, z180K30ProfileV97D6U01M0286, z180K30ProfileV97D6U01M0287, z180K30ProfileV97D6U01M0288, z180K30ProfileV97D6U01M0289, z180K30ProfileV97D6U01M0290, z180K30ProfileV97D6U01M0291, z180K30ProfileV97D6U01M0292, z180K30ProfileV97D6U01M0293, z180K30ProfileV97D6U01M0294, z180K30ProfileV97D6U01M0295, z180K30ProfileV97D6U01M0296, z180K30ProfileV97D6U01M0297, z180K30ProfileV97D6U01M0298, z180K30ProfileV97D6U01M0299]

theorem z180_k30_projective_d6_u_validity_members_u01c14_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C14PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C14PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0280_profile (And.intro z180K30ProfileV97D6U01M0281_profile (And.intro z180K30ProfileV97D6U01M0282_profile (And.intro z180K30ProfileV97D6U01M0283_profile (And.intro z180K30ProfileV97D6U01M0284_profile (And.intro z180K30ProfileV97D6U01M0285_profile (And.intro z180K30ProfileV97D6U01M0286_profile (And.intro z180K30ProfileV97D6U01M0287_profile (And.intro z180K30ProfileV97D6U01M0288_profile (And.intro z180K30ProfileV97D6U01M0289_profile (And.intro z180K30ProfileV97D6U01M0290_profile (And.intro z180K30ProfileV97D6U01M0291_profile (And.intro z180K30ProfileV97D6U01M0292_profile (And.intro z180K30ProfileV97D6U01M0293_profile (And.intro z180K30ProfileV97D6U01M0294_profile (And.intro z180K30ProfileV97D6U01M0295_profile (And.intro z180K30ProfileV97D6U01M0296_profile (And.intro z180K30ProfileV97D6U01M0297_profile (And.intro z180K30ProfileV97D6U01M0298_profile (z180K30ProfileV97D6U01M0299_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
