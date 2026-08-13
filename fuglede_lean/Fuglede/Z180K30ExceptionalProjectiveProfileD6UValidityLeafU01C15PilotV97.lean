import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S015
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S016

/-! Bounded D6 U-validity leaf U01C15: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C15PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0300, z180K30ProfileV97D6U01M0301, z180K30ProfileV97D6U01M0302, z180K30ProfileV97D6U01M0303, z180K30ProfileV97D6U01M0304, z180K30ProfileV97D6U01M0305, z180K30ProfileV97D6U01M0306, z180K30ProfileV97D6U01M0307, z180K30ProfileV97D6U01M0308, z180K30ProfileV97D6U01M0309, z180K30ProfileV97D6U01M0310, z180K30ProfileV97D6U01M0311, z180K30ProfileV97D6U01M0312, z180K30ProfileV97D6U01M0313, z180K30ProfileV97D6U01M0314, z180K30ProfileV97D6U01M0315, z180K30ProfileV97D6U01M0316, z180K30ProfileV97D6U01M0317, z180K30ProfileV97D6U01M0318, z180K30ProfileV97D6U01M0319]

theorem z180_k30_projective_d6_u_validity_members_u01c15_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C15PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C15PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0300_profile (And.intro z180K30ProfileV97D6U01M0301_profile (And.intro z180K30ProfileV97D6U01M0302_profile (And.intro z180K30ProfileV97D6U01M0303_profile (And.intro z180K30ProfileV97D6U01M0304_profile (And.intro z180K30ProfileV97D6U01M0305_profile (And.intro z180K30ProfileV97D6U01M0306_profile (And.intro z180K30ProfileV97D6U01M0307_profile (And.intro z180K30ProfileV97D6U01M0308_profile (And.intro z180K30ProfileV97D6U01M0309_profile (And.intro z180K30ProfileV97D6U01M0310_profile (And.intro z180K30ProfileV97D6U01M0311_profile (And.intro z180K30ProfileV97D6U01M0312_profile (And.intro z180K30ProfileV97D6U01M0313_profile (And.intro z180K30ProfileV97D6U01M0314_profile (And.intro z180K30ProfileV97D6U01M0315_profile (And.intro z180K30ProfileV97D6U01M0316_profile (And.intro z180K30ProfileV97D6U01M0317_profile (And.intro z180K30ProfileV97D6U01M0318_profile (z180K30ProfileV97D6U01M0319_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
