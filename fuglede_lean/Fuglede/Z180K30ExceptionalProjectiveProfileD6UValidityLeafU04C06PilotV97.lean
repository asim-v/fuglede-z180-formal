import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S052
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S053

/-! Bounded D6 U-validity leaf U04C06: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C06PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0120, z180K30ProfileV97D6U04M0121, z180K30ProfileV97D6U04M0122, z180K30ProfileV97D6U04M0123, z180K30ProfileV97D6U04M0124, z180K30ProfileV97D6U04M0125, z180K30ProfileV97D6U04M0126, z180K30ProfileV97D6U04M0127, z180K30ProfileV97D6U04M0128, z180K30ProfileV97D6U04M0129, z180K30ProfileV97D6U04M0130, z180K30ProfileV97D6U04M0131, z180K30ProfileV97D6U04M0132, z180K30ProfileV97D6U04M0133, z180K30ProfileV97D6U04M0134, z180K30ProfileV97D6U04M0135, z180K30ProfileV97D6U04M0136, z180K30ProfileV97D6U04M0137, z180K30ProfileV97D6U04M0138, z180K30ProfileV97D6U04M0139]

theorem z180_k30_projective_d6_u_validity_members_u04c06_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C06PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C06PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0120_profile (And.intro z180K30ProfileV97D6U04M0121_profile (And.intro z180K30ProfileV97D6U04M0122_profile (And.intro z180K30ProfileV97D6U04M0123_profile (And.intro z180K30ProfileV97D6U04M0124_profile (And.intro z180K30ProfileV97D6U04M0125_profile (And.intro z180K30ProfileV97D6U04M0126_profile (And.intro z180K30ProfileV97D6U04M0127_profile (And.intro z180K30ProfileV97D6U04M0128_profile (And.intro z180K30ProfileV97D6U04M0129_profile (And.intro z180K30ProfileV97D6U04M0130_profile (And.intro z180K30ProfileV97D6U04M0131_profile (And.intro z180K30ProfileV97D6U04M0132_profile (And.intro z180K30ProfileV97D6U04M0133_profile (And.intro z180K30ProfileV97D6U04M0134_profile (And.intro z180K30ProfileV97D6U04M0135_profile (And.intro z180K30ProfileV97D6U04M0136_profile (And.intro z180K30ProfileV97D6U04M0137_profile (And.intro z180K30ProfileV97D6U04M0138_profile (z180K30ProfileV97D6U04M0139_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
