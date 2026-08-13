import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S002
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S003

/-! Bounded D6 U-validity leaf U01C02: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C02PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0040, z180K30ProfileV97D6U01M0041, z180K30ProfileV97D6U01M0042, z180K30ProfileV97D6U01M0043, z180K30ProfileV97D6U01M0044, z180K30ProfileV97D6U01M0045, z180K30ProfileV97D6U01M0046, z180K30ProfileV97D6U01M0047, z180K30ProfileV97D6U01M0048, z180K30ProfileV97D6U01M0049, z180K30ProfileV97D6U01M0050, z180K30ProfileV97D6U01M0051, z180K30ProfileV97D6U01M0052, z180K30ProfileV97D6U01M0053, z180K30ProfileV97D6U01M0054, z180K30ProfileV97D6U01M0055, z180K30ProfileV97D6U01M0056, z180K30ProfileV97D6U01M0057, z180K30ProfileV97D6U01M0058, z180K30ProfileV97D6U01M0059]

theorem z180_k30_projective_d6_u_validity_members_u01c02_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C02PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C02PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0040_profile (And.intro z180K30ProfileV97D6U01M0041_profile (And.intro z180K30ProfileV97D6U01M0042_profile (And.intro z180K30ProfileV97D6U01M0043_profile (And.intro z180K30ProfileV97D6U01M0044_profile (And.intro z180K30ProfileV97D6U01M0045_profile (And.intro z180K30ProfileV97D6U01M0046_profile (And.intro z180K30ProfileV97D6U01M0047_profile (And.intro z180K30ProfileV97D6U01M0048_profile (And.intro z180K30ProfileV97D6U01M0049_profile (And.intro z180K30ProfileV97D6U01M0050_profile (And.intro z180K30ProfileV97D6U01M0051_profile (And.intro z180K30ProfileV97D6U01M0052_profile (And.intro z180K30ProfileV97D6U01M0053_profile (And.intro z180K30ProfileV97D6U01M0054_profile (And.intro z180K30ProfileV97D6U01M0055_profile (And.intro z180K30ProfileV97D6U01M0056_profile (And.intro z180K30ProfileV97D6U01M0057_profile (And.intro z180K30ProfileV97D6U01M0058_profile (z180K30ProfileV97D6U01M0059_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
