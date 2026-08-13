import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S016
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S017

/-! Bounded D6 U-validity leaf U01C16: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C16PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0320, z180K30ProfileV97D6U01M0321, z180K30ProfileV97D6U01M0322, z180K30ProfileV97D6U01M0323, z180K30ProfileV97D6U01M0324, z180K30ProfileV97D6U01M0325, z180K30ProfileV97D6U01M0326, z180K30ProfileV97D6U01M0327, z180K30ProfileV97D6U01M0328, z180K30ProfileV97D6U01M0329, z180K30ProfileV97D6U01M0330, z180K30ProfileV97D6U01M0331, z180K30ProfileV97D6U01M0332, z180K30ProfileV97D6U01M0333, z180K30ProfileV97D6U01M0334, z180K30ProfileV97D6U01M0335, z180K30ProfileV97D6U01M0336, z180K30ProfileV97D6U01M0337, z180K30ProfileV97D6U01M0338, z180K30ProfileV97D6U01M0339]

theorem z180_k30_projective_d6_u_validity_members_u01c16_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C16PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C16PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0320_profile (And.intro z180K30ProfileV97D6U01M0321_profile (And.intro z180K30ProfileV97D6U01M0322_profile (And.intro z180K30ProfileV97D6U01M0323_profile (And.intro z180K30ProfileV97D6U01M0324_profile (And.intro z180K30ProfileV97D6U01M0325_profile (And.intro z180K30ProfileV97D6U01M0326_profile (And.intro z180K30ProfileV97D6U01M0327_profile (And.intro z180K30ProfileV97D6U01M0328_profile (And.intro z180K30ProfileV97D6U01M0329_profile (And.intro z180K30ProfileV97D6U01M0330_profile (And.intro z180K30ProfileV97D6U01M0331_profile (And.intro z180K30ProfileV97D6U01M0332_profile (And.intro z180K30ProfileV97D6U01M0333_profile (And.intro z180K30ProfileV97D6U01M0334_profile (And.intro z180K30ProfileV97D6U01M0335_profile (And.intro z180K30ProfileV97D6U01M0336_profile (And.intro z180K30ProfileV97D6U01M0337_profile (And.intro z180K30ProfileV97D6U01M0338_profile (z180K30ProfileV97D6U01M0339_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
