import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S098
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S099

/-! Bounded D6 U-validity leaf U07C06: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07C06PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U07M0120, z180K30ProfileV97D6U07M0121, z180K30ProfileV97D6U07M0122, z180K30ProfileV97D6U07M0123, z180K30ProfileV97D6U07M0124, z180K30ProfileV97D6U07M0125, z180K30ProfileV97D6U07M0126, z180K30ProfileV97D6U07M0127, z180K30ProfileV97D6U07M0128, z180K30ProfileV97D6U07M0129, z180K30ProfileV97D6U07M0130, z180K30ProfileV97D6U07M0131, z180K30ProfileV97D6U07M0132, z180K30ProfileV97D6U07M0133, z180K30ProfileV97D6U07M0134, z180K30ProfileV97D6U07M0135, z180K30ProfileV97D6U07M0136, z180K30ProfileV97D6U07M0137, z180K30ProfileV97D6U07M0138, z180K30ProfileV97D6U07M0139]

theorem z180_k30_projective_d6_u_validity_members_u07c06_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07C06PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07C06PilotV97 z180K30ProjectiveD6UValidityProfileU07PilotV97
  exact And.intro z180K30ProfileV97D6U07M0120_profile (And.intro z180K30ProfileV97D6U07M0121_profile (And.intro z180K30ProfileV97D6U07M0122_profile (And.intro z180K30ProfileV97D6U07M0123_profile (And.intro z180K30ProfileV97D6U07M0124_profile (And.intro z180K30ProfileV97D6U07M0125_profile (And.intro z180K30ProfileV97D6U07M0126_profile (And.intro z180K30ProfileV97D6U07M0127_profile (And.intro z180K30ProfileV97D6U07M0128_profile (And.intro z180K30ProfileV97D6U07M0129_profile (And.intro z180K30ProfileV97D6U07M0130_profile (And.intro z180K30ProfileV97D6U07M0131_profile (And.intro z180K30ProfileV97D6U07M0132_profile (And.intro z180K30ProfileV97D6U07M0133_profile (And.intro z180K30ProfileV97D6U07M0134_profile (And.intro z180K30ProfileV97D6U07M0135_profile (And.intro z180K30ProfileV97D6U07M0136_profile (And.intro z180K30ProfileV97D6U07M0137_profile (And.intro z180K30ProfileV97D6U07M0138_profile (z180K30ProfileV97D6U07M0139_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
