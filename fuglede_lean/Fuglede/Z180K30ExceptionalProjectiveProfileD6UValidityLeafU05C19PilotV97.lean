import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S085
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S086

/-! Bounded D6 U-validity leaf U05C19: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C19PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0380, z180K30ProfileV97D6U05M0381, z180K30ProfileV97D6U05M0382, z180K30ProfileV97D6U05M0383, z180K30ProfileV97D6U05M0384, z180K30ProfileV97D6U05M0385, z180K30ProfileV97D6U05M0386, z180K30ProfileV97D6U05M0387, z180K30ProfileV97D6U05M0388, z180K30ProfileV97D6U05M0389, z180K30ProfileV97D6U05M0390, z180K30ProfileV97D6U05M0391, z180K30ProfileV97D6U05M0392, z180K30ProfileV97D6U05M0393, z180K30ProfileV97D6U05M0394, z180K30ProfileV97D6U05M0395, z180K30ProfileV97D6U05M0396, z180K30ProfileV97D6U05M0397, z180K30ProfileV97D6U05M0398, z180K30ProfileV97D6U05M0399]

theorem z180_k30_projective_d6_u_validity_members_u05c19_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C19PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C19PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0380_profile (And.intro z180K30ProfileV97D6U05M0381_profile (And.intro z180K30ProfileV97D6U05M0382_profile (And.intro z180K30ProfileV97D6U05M0383_profile (And.intro z180K30ProfileV97D6U05M0384_profile (And.intro z180K30ProfileV97D6U05M0385_profile (And.intro z180K30ProfileV97D6U05M0386_profile (And.intro z180K30ProfileV97D6U05M0387_profile (And.intro z180K30ProfileV97D6U05M0388_profile (And.intro z180K30ProfileV97D6U05M0389_profile (And.intro z180K30ProfileV97D6U05M0390_profile (And.intro z180K30ProfileV97D6U05M0391_profile (And.intro z180K30ProfileV97D6U05M0392_profile (And.intro z180K30ProfileV97D6U05M0393_profile (And.intro z180K30ProfileV97D6U05M0394_profile (And.intro z180K30ProfileV97D6U05M0395_profile (And.intro z180K30ProfileV97D6U05M0396_profile (And.intro z180K30ProfileV97D6U05M0397_profile (And.intro z180K30ProfileV97D6U05M0398_profile (z180K30ProfileV97D6U05M0399_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
