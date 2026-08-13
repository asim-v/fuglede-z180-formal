import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S088

/-! Bounded D6 U-validity leaf U05C22: 10 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C22PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0440, z180K30ProfileV97D6U05M0441, z180K30ProfileV97D6U05M0442, z180K30ProfileV97D6U05M0443, z180K30ProfileV97D6U05M0444, z180K30ProfileV97D6U05M0445, z180K30ProfileV97D6U05M0446, z180K30ProfileV97D6U05M0447, z180K30ProfileV97D6U05M0448, z180K30ProfileV97D6U05M0449]

theorem z180_k30_projective_d6_u_validity_members_u05c22_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C22PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C22PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0440_profile (And.intro z180K30ProfileV97D6U05M0441_profile (And.intro z180K30ProfileV97D6U05M0442_profile (And.intro z180K30ProfileV97D6U05M0443_profile (And.intro z180K30ProfileV97D6U05M0444_profile (And.intro z180K30ProfileV97D6U05M0445_profile (And.intro z180K30ProfileV97D6U05M0446_profile (And.intro z180K30ProfileV97D6U05M0447_profile (And.intro z180K30ProfileV97D6U05M0448_profile (z180K30ProfileV97D6U05M0449_profile)))))))))

end Fuglede.Z180K30ExceptionalRawV2
