import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S023
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S024

/-! Bounded D6 U-validity leaf U02C03: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C03PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0060, z180K30ProfileV97D6U02M0061, z180K30ProfileV97D6U02M0062, z180K30ProfileV97D6U02M0063, z180K30ProfileV97D6U02M0064, z180K30ProfileV97D6U02M0065, z180K30ProfileV97D6U02M0066, z180K30ProfileV97D6U02M0067, z180K30ProfileV97D6U02M0068, z180K30ProfileV97D6U02M0069, z180K30ProfileV97D6U02M0070, z180K30ProfileV97D6U02M0071, z180K30ProfileV97D6U02M0072, z180K30ProfileV97D6U02M0073, z180K30ProfileV97D6U02M0074, z180K30ProfileV97D6U02M0075, z180K30ProfileV97D6U02M0076, z180K30ProfileV97D6U02M0077, z180K30ProfileV97D6U02M0078, z180K30ProfileV97D6U02M0079]

theorem z180_k30_projective_d6_u_validity_members_u02c03_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C03PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C03PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0060_profile (And.intro z180K30ProfileV97D6U02M0061_profile (And.intro z180K30ProfileV97D6U02M0062_profile (And.intro z180K30ProfileV97D6U02M0063_profile (And.intro z180K30ProfileV97D6U02M0064_profile (And.intro z180K30ProfileV97D6U02M0065_profile (And.intro z180K30ProfileV97D6U02M0066_profile (And.intro z180K30ProfileV97D6U02M0067_profile (And.intro z180K30ProfileV97D6U02M0068_profile (And.intro z180K30ProfileV97D6U02M0069_profile (And.intro z180K30ProfileV97D6U02M0070_profile (And.intro z180K30ProfileV97D6U02M0071_profile (And.intro z180K30ProfileV97D6U02M0072_profile (And.intro z180K30ProfileV97D6U02M0073_profile (And.intro z180K30ProfileV97D6U02M0074_profile (And.intro z180K30ProfileV97D6U02M0075_profile (And.intro z180K30ProfileV97D6U02M0076_profile (And.intro z180K30ProfileV97D6U02M0077_profile (And.intro z180K30ProfileV97D6U02M0078_profile (z180K30ProfileV97D6U02M0079_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
