import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S045
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S046

/-! Bounded D6 U-validity leaf U03C03: 12 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU03C03PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U03M0060, z180K30ProfileV97D6U03M0061, z180K30ProfileV97D6U03M0062, z180K30ProfileV97D6U03M0063, z180K30ProfileV97D6U03M0064, z180K30ProfileV97D6U03M0065, z180K30ProfileV97D6U03M0066, z180K30ProfileV97D6U03M0067, z180K30ProfileV97D6U03M0068, z180K30ProfileV97D6U03M0069, z180K30ProfileV97D6U03M0070, z180K30ProfileV97D6U03M0071]

theorem z180_k30_projective_d6_u_validity_members_u03c03_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU03PilotV97)
      z180K30ProjectiveD6UValidityMembersU03C03PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU03C03PilotV97 z180K30ProjectiveD6UValidityProfileU03PilotV97
  exact And.intro z180K30ProfileV97D6U03M0060_profile (And.intro z180K30ProfileV97D6U03M0061_profile (And.intro z180K30ProfileV97D6U03M0062_profile (And.intro z180K30ProfileV97D6U03M0063_profile (And.intro z180K30ProfileV97D6U03M0064_profile (And.intro z180K30ProfileV97D6U03M0065_profile (And.intro z180K30ProfileV97D6U03M0066_profile (And.intro z180K30ProfileV97D6U03M0067_profile (And.intro z180K30ProfileV97D6U03M0068_profile (And.intro z180K30ProfileV97D6U03M0069_profile (And.intro z180K30ProfileV97D6U03M0070_profile (z180K30ProfileV97D6U03M0071_profile)))))))))))

end Fuglede.Z180K30ExceptionalRawV2
