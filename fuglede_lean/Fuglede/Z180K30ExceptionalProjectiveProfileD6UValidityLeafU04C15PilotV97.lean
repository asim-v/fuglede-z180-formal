import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S061
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S062

/-! Bounded D6 U-validity leaf U04C15: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C15PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0300, z180K30ProfileV97D6U04M0301, z180K30ProfileV97D6U04M0302, z180K30ProfileV97D6U04M0303, z180K30ProfileV97D6U04M0304, z180K30ProfileV97D6U04M0305, z180K30ProfileV97D6U04M0306, z180K30ProfileV97D6U04M0307, z180K30ProfileV97D6U04M0308, z180K30ProfileV97D6U04M0309, z180K30ProfileV97D6U04M0310, z180K30ProfileV97D6U04M0311, z180K30ProfileV97D6U04M0312, z180K30ProfileV97D6U04M0313, z180K30ProfileV97D6U04M0314, z180K30ProfileV97D6U04M0315, z180K30ProfileV97D6U04M0316, z180K30ProfileV97D6U04M0317, z180K30ProfileV97D6U04M0318, z180K30ProfileV97D6U04M0319]

theorem z180_k30_projective_d6_u_validity_members_u04c15_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C15PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C15PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0300_profile (And.intro z180K30ProfileV97D6U04M0301_profile (And.intro z180K30ProfileV97D6U04M0302_profile (And.intro z180K30ProfileV97D6U04M0303_profile (And.intro z180K30ProfileV97D6U04M0304_profile (And.intro z180K30ProfileV97D6U04M0305_profile (And.intro z180K30ProfileV97D6U04M0306_profile (And.intro z180K30ProfileV97D6U04M0307_profile (And.intro z180K30ProfileV97D6U04M0308_profile (And.intro z180K30ProfileV97D6U04M0309_profile (And.intro z180K30ProfileV97D6U04M0310_profile (And.intro z180K30ProfileV97D6U04M0311_profile (And.intro z180K30ProfileV97D6U04M0312_profile (And.intro z180K30ProfileV97D6U04M0313_profile (And.intro z180K30ProfileV97D6U04M0314_profile (And.intro z180K30ProfileV97D6U04M0315_profile (And.intro z180K30ProfileV97D6U04M0316_profile (And.intro z180K30ProfileV97D6U04M0317_profile (And.intro z180K30ProfileV97D6U04M0318_profile (z180K30ProfileV97D6U04M0319_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
