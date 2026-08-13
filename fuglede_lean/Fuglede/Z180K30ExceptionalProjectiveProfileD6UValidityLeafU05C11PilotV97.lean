import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S077
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S078

/-! Bounded D6 U-validity leaf U05C11: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C11PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0220, z180K30ProfileV97D6U05M0221, z180K30ProfileV97D6U05M0222, z180K30ProfileV97D6U05M0223, z180K30ProfileV97D6U05M0224, z180K30ProfileV97D6U05M0225, z180K30ProfileV97D6U05M0226, z180K30ProfileV97D6U05M0227, z180K30ProfileV97D6U05M0228, z180K30ProfileV97D6U05M0229, z180K30ProfileV97D6U05M0230, z180K30ProfileV97D6U05M0231, z180K30ProfileV97D6U05M0232, z180K30ProfileV97D6U05M0233, z180K30ProfileV97D6U05M0234, z180K30ProfileV97D6U05M0235, z180K30ProfileV97D6U05M0236, z180K30ProfileV97D6U05M0237, z180K30ProfileV97D6U05M0238, z180K30ProfileV97D6U05M0239]

theorem z180_k30_projective_d6_u_validity_members_u05c11_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C11PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C11PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0220_profile (And.intro z180K30ProfileV97D6U05M0221_profile (And.intro z180K30ProfileV97D6U05M0222_profile (And.intro z180K30ProfileV97D6U05M0223_profile (And.intro z180K30ProfileV97D6U05M0224_profile (And.intro z180K30ProfileV97D6U05M0225_profile (And.intro z180K30ProfileV97D6U05M0226_profile (And.intro z180K30ProfileV97D6U05M0227_profile (And.intro z180K30ProfileV97D6U05M0228_profile (And.intro z180K30ProfileV97D6U05M0229_profile (And.intro z180K30ProfileV97D6U05M0230_profile (And.intro z180K30ProfileV97D6U05M0231_profile (And.intro z180K30ProfileV97D6U05M0232_profile (And.intro z180K30ProfileV97D6U05M0233_profile (And.intro z180K30ProfileV97D6U05M0234_profile (And.intro z180K30ProfileV97D6U05M0235_profile (And.intro z180K30ProfileV97D6U05M0236_profile (And.intro z180K30ProfileV97D6U05M0237_profile (And.intro z180K30ProfileV97D6U05M0238_profile (z180K30ProfileV97D6U05M0239_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
