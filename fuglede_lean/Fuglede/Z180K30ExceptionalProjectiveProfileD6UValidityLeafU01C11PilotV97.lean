import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S011
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S012

/-! Bounded D6 U-validity leaf U01C11: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C11PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0220, z180K30ProfileV97D6U01M0221, z180K30ProfileV97D6U01M0222, z180K30ProfileV97D6U01M0223, z180K30ProfileV97D6U01M0224, z180K30ProfileV97D6U01M0225, z180K30ProfileV97D6U01M0226, z180K30ProfileV97D6U01M0227, z180K30ProfileV97D6U01M0228, z180K30ProfileV97D6U01M0229, z180K30ProfileV97D6U01M0230, z180K30ProfileV97D6U01M0231, z180K30ProfileV97D6U01M0232, z180K30ProfileV97D6U01M0233, z180K30ProfileV97D6U01M0234, z180K30ProfileV97D6U01M0235, z180K30ProfileV97D6U01M0236, z180K30ProfileV97D6U01M0237, z180K30ProfileV97D6U01M0238, z180K30ProfileV97D6U01M0239]

theorem z180_k30_projective_d6_u_validity_members_u01c11_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C11PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C11PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0220_profile (And.intro z180K30ProfileV97D6U01M0221_profile (And.intro z180K30ProfileV97D6U01M0222_profile (And.intro z180K30ProfileV97D6U01M0223_profile (And.intro z180K30ProfileV97D6U01M0224_profile (And.intro z180K30ProfileV97D6U01M0225_profile (And.intro z180K30ProfileV97D6U01M0226_profile (And.intro z180K30ProfileV97D6U01M0227_profile (And.intro z180K30ProfileV97D6U01M0228_profile (And.intro z180K30ProfileV97D6U01M0229_profile (And.intro z180K30ProfileV97D6U01M0230_profile (And.intro z180K30ProfileV97D6U01M0231_profile (And.intro z180K30ProfileV97D6U01M0232_profile (And.intro z180K30ProfileV97D6U01M0233_profile (And.intro z180K30ProfileV97D6U01M0234_profile (And.intro z180K30ProfileV97D6U01M0235_profile (And.intro z180K30ProfileV97D6U01M0236_profile (And.intro z180K30ProfileV97D6U01M0237_profile (And.intro z180K30ProfileV97D6U01M0238_profile (z180K30ProfileV97D6U01M0239_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
