import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S065
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S066

/-! Bounded D6 U-validity leaf U04C19: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C19PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0380, z180K30ProfileV97D6U04M0381, z180K30ProfileV97D6U04M0382, z180K30ProfileV97D6U04M0383, z180K30ProfileV97D6U04M0384, z180K30ProfileV97D6U04M0385, z180K30ProfileV97D6U04M0386, z180K30ProfileV97D6U04M0387, z180K30ProfileV97D6U04M0388, z180K30ProfileV97D6U04M0389, z180K30ProfileV97D6U04M0390, z180K30ProfileV97D6U04M0391, z180K30ProfileV97D6U04M0392, z180K30ProfileV97D6U04M0393, z180K30ProfileV97D6U04M0394, z180K30ProfileV97D6U04M0395, z180K30ProfileV97D6U04M0396, z180K30ProfileV97D6U04M0397, z180K30ProfileV97D6U04M0398, z180K30ProfileV97D6U04M0399]

theorem z180_k30_projective_d6_u_validity_members_u04c19_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C19PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C19PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0380_profile (And.intro z180K30ProfileV97D6U04M0381_profile (And.intro z180K30ProfileV97D6U04M0382_profile (And.intro z180K30ProfileV97D6U04M0383_profile (And.intro z180K30ProfileV97D6U04M0384_profile (And.intro z180K30ProfileV97D6U04M0385_profile (And.intro z180K30ProfileV97D6U04M0386_profile (And.intro z180K30ProfileV97D6U04M0387_profile (And.intro z180K30ProfileV97D6U04M0388_profile (And.intro z180K30ProfileV97D6U04M0389_profile (And.intro z180K30ProfileV97D6U04M0390_profile (And.intro z180K30ProfileV97D6U04M0391_profile (And.intro z180K30ProfileV97D6U04M0392_profile (And.intro z180K30ProfileV97D6U04M0393_profile (And.intro z180K30ProfileV97D6U04M0394_profile (And.intro z180K30ProfileV97D6U04M0395_profile (And.intro z180K30ProfileV97D6U04M0396_profile (And.intro z180K30ProfileV97D6U04M0397_profile (And.intro z180K30ProfileV97D6U04M0398_profile (z180K30ProfileV97D6U04M0399_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
