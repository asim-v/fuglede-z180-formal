import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S069
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S070

/-! Bounded D6 U-validity leaf U05C03: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C03PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0060, z180K30ProfileV97D6U05M0061, z180K30ProfileV97D6U05M0062, z180K30ProfileV97D6U05M0063, z180K30ProfileV97D6U05M0064, z180K30ProfileV97D6U05M0065, z180K30ProfileV97D6U05M0066, z180K30ProfileV97D6U05M0067, z180K30ProfileV97D6U05M0068, z180K30ProfileV97D6U05M0069, z180K30ProfileV97D6U05M0070, z180K30ProfileV97D6U05M0071, z180K30ProfileV97D6U05M0072, z180K30ProfileV97D6U05M0073, z180K30ProfileV97D6U05M0074, z180K30ProfileV97D6U05M0075, z180K30ProfileV97D6U05M0076, z180K30ProfileV97D6U05M0077, z180K30ProfileV97D6U05M0078, z180K30ProfileV97D6U05M0079]

theorem z180_k30_projective_d6_u_validity_members_u05c03_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C03PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C03PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0060_profile (And.intro z180K30ProfileV97D6U05M0061_profile (And.intro z180K30ProfileV97D6U05M0062_profile (And.intro z180K30ProfileV97D6U05M0063_profile (And.intro z180K30ProfileV97D6U05M0064_profile (And.intro z180K30ProfileV97D6U05M0065_profile (And.intro z180K30ProfileV97D6U05M0066_profile (And.intro z180K30ProfileV97D6U05M0067_profile (And.intro z180K30ProfileV97D6U05M0068_profile (And.intro z180K30ProfileV97D6U05M0069_profile (And.intro z180K30ProfileV97D6U05M0070_profile (And.intro z180K30ProfileV97D6U05M0071_profile (And.intro z180K30ProfileV97D6U05M0072_profile (And.intro z180K30ProfileV97D6U05M0073_profile (And.intro z180K30ProfileV97D6U05M0074_profile (And.intro z180K30ProfileV97D6U05M0075_profile (And.intro z180K30ProfileV97D6U05M0076_profile (And.intro z180K30ProfileV97D6U05M0077_profile (And.intro z180K30ProfileV97D6U05M0078_profile (z180K30ProfileV97D6U05M0079_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
