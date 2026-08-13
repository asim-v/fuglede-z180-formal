import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S094
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S095

/-! Bounded D6 U-validity leaf U07C02: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07C02PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U07M0040, z180K30ProfileV97D6U07M0041, z180K30ProfileV97D6U07M0042, z180K30ProfileV97D6U07M0043, z180K30ProfileV97D6U07M0044, z180K30ProfileV97D6U07M0045, z180K30ProfileV97D6U07M0046, z180K30ProfileV97D6U07M0047, z180K30ProfileV97D6U07M0048, z180K30ProfileV97D6U07M0049, z180K30ProfileV97D6U07M0050, z180K30ProfileV97D6U07M0051, z180K30ProfileV97D6U07M0052, z180K30ProfileV97D6U07M0053, z180K30ProfileV97D6U07M0054, z180K30ProfileV97D6U07M0055, z180K30ProfileV97D6U07M0056, z180K30ProfileV97D6U07M0057, z180K30ProfileV97D6U07M0058, z180K30ProfileV97D6U07M0059]

theorem z180_k30_projective_d6_u_validity_members_u07c02_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07C02PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07C02PilotV97 z180K30ProjectiveD6UValidityProfileU07PilotV97
  exact And.intro z180K30ProfileV97D6U07M0040_profile (And.intro z180K30ProfileV97D6U07M0041_profile (And.intro z180K30ProfileV97D6U07M0042_profile (And.intro z180K30ProfileV97D6U07M0043_profile (And.intro z180K30ProfileV97D6U07M0044_profile (And.intro z180K30ProfileV97D6U07M0045_profile (And.intro z180K30ProfileV97D6U07M0046_profile (And.intro z180K30ProfileV97D6U07M0047_profile (And.intro z180K30ProfileV97D6U07M0048_profile (And.intro z180K30ProfileV97D6U07M0049_profile (And.intro z180K30ProfileV97D6U07M0050_profile (And.intro z180K30ProfileV97D6U07M0051_profile (And.intro z180K30ProfileV97D6U07M0052_profile (And.intro z180K30ProfileV97D6U07M0053_profile (And.intro z180K30ProfileV97D6U07M0054_profile (And.intro z180K30ProfileV97D6U07M0055_profile (And.intro z180K30ProfileV97D6U07M0056_profile (And.intro z180K30ProfileV97D6U07M0057_profile (And.intro z180K30ProfileV97D6U07M0058_profile (z180K30ProfileV97D6U07M0059_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
