import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S081
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S082

/-! Bounded D6 U-validity leaf U05C15: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C15PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0300, z180K30ProfileV97D6U05M0301, z180K30ProfileV97D6U05M0302, z180K30ProfileV97D6U05M0303, z180K30ProfileV97D6U05M0304, z180K30ProfileV97D6U05M0305, z180K30ProfileV97D6U05M0306, z180K30ProfileV97D6U05M0307, z180K30ProfileV97D6U05M0308, z180K30ProfileV97D6U05M0309, z180K30ProfileV97D6U05M0310, z180K30ProfileV97D6U05M0311, z180K30ProfileV97D6U05M0312, z180K30ProfileV97D6U05M0313, z180K30ProfileV97D6U05M0314, z180K30ProfileV97D6U05M0315, z180K30ProfileV97D6U05M0316, z180K30ProfileV97D6U05M0317, z180K30ProfileV97D6U05M0318, z180K30ProfileV97D6U05M0319]

theorem z180_k30_projective_d6_u_validity_members_u05c15_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C15PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C15PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0300_profile (And.intro z180K30ProfileV97D6U05M0301_profile (And.intro z180K30ProfileV97D6U05M0302_profile (And.intro z180K30ProfileV97D6U05M0303_profile (And.intro z180K30ProfileV97D6U05M0304_profile (And.intro z180K30ProfileV97D6U05M0305_profile (And.intro z180K30ProfileV97D6U05M0306_profile (And.intro z180K30ProfileV97D6U05M0307_profile (And.intro z180K30ProfileV97D6U05M0308_profile (And.intro z180K30ProfileV97D6U05M0309_profile (And.intro z180K30ProfileV97D6U05M0310_profile (And.intro z180K30ProfileV97D6U05M0311_profile (And.intro z180K30ProfileV97D6U05M0312_profile (And.intro z180K30ProfileV97D6U05M0313_profile (And.intro z180K30ProfileV97D6U05M0314_profile (And.intro z180K30ProfileV97D6U05M0315_profile (And.intro z180K30ProfileV97D6U05M0316_profile (And.intro z180K30ProfileV97D6U05M0317_profile (And.intro z180K30ProfileV97D6U05M0318_profile (z180K30ProfileV97D6U05M0319_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
