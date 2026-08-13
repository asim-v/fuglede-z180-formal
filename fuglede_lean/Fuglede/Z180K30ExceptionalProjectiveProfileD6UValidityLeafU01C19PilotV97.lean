import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S019
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S020

/-! Bounded D6 U-validity leaf U01C19: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C19PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0380, z180K30ProfileV97D6U01M0381, z180K30ProfileV97D6U01M0382, z180K30ProfileV97D6U01M0383, z180K30ProfileV97D6U01M0384, z180K30ProfileV97D6U01M0385, z180K30ProfileV97D6U01M0386, z180K30ProfileV97D6U01M0387, z180K30ProfileV97D6U01M0388, z180K30ProfileV97D6U01M0389, z180K30ProfileV97D6U01M0390, z180K30ProfileV97D6U01M0391, z180K30ProfileV97D6U01M0392, z180K30ProfileV97D6U01M0393, z180K30ProfileV97D6U01M0394, z180K30ProfileV97D6U01M0395, z180K30ProfileV97D6U01M0396, z180K30ProfileV97D6U01M0397, z180K30ProfileV97D6U01M0398, z180K30ProfileV97D6U01M0399]

theorem z180_k30_projective_d6_u_validity_members_u01c19_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C19PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C19PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0380_profile (And.intro z180K30ProfileV97D6U01M0381_profile (And.intro z180K30ProfileV97D6U01M0382_profile (And.intro z180K30ProfileV97D6U01M0383_profile (And.intro z180K30ProfileV97D6U01M0384_profile (And.intro z180K30ProfileV97D6U01M0385_profile (And.intro z180K30ProfileV97D6U01M0386_profile (And.intro z180K30ProfileV97D6U01M0387_profile (And.intro z180K30ProfileV97D6U01M0388_profile (And.intro z180K30ProfileV97D6U01M0389_profile (And.intro z180K30ProfileV97D6U01M0390_profile (And.intro z180K30ProfileV97D6U01M0391_profile (And.intro z180K30ProfileV97D6U01M0392_profile (And.intro z180K30ProfileV97D6U01M0393_profile (And.intro z180K30ProfileV97D6U01M0394_profile (And.intro z180K30ProfileV97D6U01M0395_profile (And.intro z180K30ProfileV97D6U01M0396_profile (And.intro z180K30ProfileV97D6U01M0397_profile (And.intro z180K30ProfileV97D6U01M0398_profile (z180K30ProfileV97D6U01M0399_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
