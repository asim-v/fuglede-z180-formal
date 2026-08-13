import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S004
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S005

/-! Bounded D6 U-validity leaf U01C04: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C04PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0080, z180K30ProfileV97D6U01M0081, z180K30ProfileV97D6U01M0082, z180K30ProfileV97D6U01M0083, z180K30ProfileV97D6U01M0084, z180K30ProfileV97D6U01M0085, z180K30ProfileV97D6U01M0086, z180K30ProfileV97D6U01M0087, z180K30ProfileV97D6U01M0088, z180K30ProfileV97D6U01M0089, z180K30ProfileV97D6U01M0090, z180K30ProfileV97D6U01M0091, z180K30ProfileV97D6U01M0092, z180K30ProfileV97D6U01M0093, z180K30ProfileV97D6U01M0094, z180K30ProfileV97D6U01M0095, z180K30ProfileV97D6U01M0096, z180K30ProfileV97D6U01M0097, z180K30ProfileV97D6U01M0098, z180K30ProfileV97D6U01M0099]

theorem z180_k30_projective_d6_u_validity_members_u01c04_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C04PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C04PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0080_profile (And.intro z180K30ProfileV97D6U01M0081_profile (And.intro z180K30ProfileV97D6U01M0082_profile (And.intro z180K30ProfileV97D6U01M0083_profile (And.intro z180K30ProfileV97D6U01M0084_profile (And.intro z180K30ProfileV97D6U01M0085_profile (And.intro z180K30ProfileV97D6U01M0086_profile (And.intro z180K30ProfileV97D6U01M0087_profile (And.intro z180K30ProfileV97D6U01M0088_profile (And.intro z180K30ProfileV97D6U01M0089_profile (And.intro z180K30ProfileV97D6U01M0090_profile (And.intro z180K30ProfileV97D6U01M0091_profile (And.intro z180K30ProfileV97D6U01M0092_profile (And.intro z180K30ProfileV97D6U01M0093_profile (And.intro z180K30ProfileV97D6U01M0094_profile (And.intro z180K30ProfileV97D6U01M0095_profile (And.intro z180K30ProfileV97D6U01M0096_profile (And.intro z180K30ProfileV97D6U01M0097_profile (And.intro z180K30ProfileV97D6U01M0098_profile (z180K30ProfileV97D6U01M0099_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
