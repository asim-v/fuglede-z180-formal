import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S024
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S025

/-! Bounded D6 U-validity leaf U02C04: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C04PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0080, z180K30ProfileV97D6U02M0081, z180K30ProfileV97D6U02M0082, z180K30ProfileV97D6U02M0083, z180K30ProfileV97D6U02M0084, z180K30ProfileV97D6U02M0085, z180K30ProfileV97D6U02M0086, z180K30ProfileV97D6U02M0087, z180K30ProfileV97D6U02M0088, z180K30ProfileV97D6U02M0089, z180K30ProfileV97D6U02M0090, z180K30ProfileV97D6U02M0091, z180K30ProfileV97D6U02M0092, z180K30ProfileV97D6U02M0093, z180K30ProfileV97D6U02M0094, z180K30ProfileV97D6U02M0095, z180K30ProfileV97D6U02M0096, z180K30ProfileV97D6U02M0097, z180K30ProfileV97D6U02M0098, z180K30ProfileV97D6U02M0099]

theorem z180_k30_projective_d6_u_validity_members_u02c04_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C04PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C04PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0080_profile (And.intro z180K30ProfileV97D6U02M0081_profile (And.intro z180K30ProfileV97D6U02M0082_profile (And.intro z180K30ProfileV97D6U02M0083_profile (And.intro z180K30ProfileV97D6U02M0084_profile (And.intro z180K30ProfileV97D6U02M0085_profile (And.intro z180K30ProfileV97D6U02M0086_profile (And.intro z180K30ProfileV97D6U02M0087_profile (And.intro z180K30ProfileV97D6U02M0088_profile (And.intro z180K30ProfileV97D6U02M0089_profile (And.intro z180K30ProfileV97D6U02M0090_profile (And.intro z180K30ProfileV97D6U02M0091_profile (And.intro z180K30ProfileV97D6U02M0092_profile (And.intro z180K30ProfileV97D6U02M0093_profile (And.intro z180K30ProfileV97D6U02M0094_profile (And.intro z180K30ProfileV97D6U02M0095_profile (And.intro z180K30ProfileV97D6U02M0096_profile (And.intro z180K30ProfileV97D6U02M0097_profile (And.intro z180K30ProfileV97D6U02M0098_profile (z180K30ProfileV97D6U02M0099_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
