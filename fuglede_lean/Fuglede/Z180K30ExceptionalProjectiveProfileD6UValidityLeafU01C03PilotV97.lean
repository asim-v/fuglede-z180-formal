import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S003
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S004

/-! Bounded D6 U-validity leaf U01C03: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C03PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0060, z180K30ProfileV97D6U01M0061, z180K30ProfileV97D6U01M0062, z180K30ProfileV97D6U01M0063, z180K30ProfileV97D6U01M0064, z180K30ProfileV97D6U01M0065, z180K30ProfileV97D6U01M0066, z180K30ProfileV97D6U01M0067, z180K30ProfileV97D6U01M0068, z180K30ProfileV97D6U01M0069, z180K30ProfileV97D6U01M0070, z180K30ProfileV97D6U01M0071, z180K30ProfileV97D6U01M0072, z180K30ProfileV97D6U01M0073, z180K30ProfileV97D6U01M0074, z180K30ProfileV97D6U01M0075, z180K30ProfileV97D6U01M0076, z180K30ProfileV97D6U01M0077, z180K30ProfileV97D6U01M0078, z180K30ProfileV97D6U01M0079]

theorem z180_k30_projective_d6_u_validity_members_u01c03_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C03PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C03PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0060_profile (And.intro z180K30ProfileV97D6U01M0061_profile (And.intro z180K30ProfileV97D6U01M0062_profile (And.intro z180K30ProfileV97D6U01M0063_profile (And.intro z180K30ProfileV97D6U01M0064_profile (And.intro z180K30ProfileV97D6U01M0065_profile (And.intro z180K30ProfileV97D6U01M0066_profile (And.intro z180K30ProfileV97D6U01M0067_profile (And.intro z180K30ProfileV97D6U01M0068_profile (And.intro z180K30ProfileV97D6U01M0069_profile (And.intro z180K30ProfileV97D6U01M0070_profile (And.intro z180K30ProfileV97D6U01M0071_profile (And.intro z180K30ProfileV97D6U01M0072_profile (And.intro z180K30ProfileV97D6U01M0073_profile (And.intro z180K30ProfileV97D6U01M0074_profile (And.intro z180K30ProfileV97D6U01M0075_profile (And.intro z180K30ProfileV97D6U01M0076_profile (And.intro z180K30ProfileV97D6U01M0077_profile (And.intro z180K30ProfileV97D6U01M0078_profile (z180K30ProfileV97D6U01M0079_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
