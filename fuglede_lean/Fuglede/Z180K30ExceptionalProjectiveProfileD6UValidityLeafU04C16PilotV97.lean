import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S062
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S063

/-! Bounded D6 U-validity leaf U04C16: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C16PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0320, z180K30ProfileV97D6U04M0321, z180K30ProfileV97D6U04M0322, z180K30ProfileV97D6U04M0323, z180K30ProfileV97D6U04M0324, z180K30ProfileV97D6U04M0325, z180K30ProfileV97D6U04M0326, z180K30ProfileV97D6U04M0327, z180K30ProfileV97D6U04M0328, z180K30ProfileV97D6U04M0329, z180K30ProfileV97D6U04M0330, z180K30ProfileV97D6U04M0331, z180K30ProfileV97D6U04M0332, z180K30ProfileV97D6U04M0333, z180K30ProfileV97D6U04M0334, z180K30ProfileV97D6U04M0335, z180K30ProfileV97D6U04M0336, z180K30ProfileV97D6U04M0337, z180K30ProfileV97D6U04M0338, z180K30ProfileV97D6U04M0339]

theorem z180_k30_projective_d6_u_validity_members_u04c16_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C16PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C16PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0320_profile (And.intro z180K30ProfileV97D6U04M0321_profile (And.intro z180K30ProfileV97D6U04M0322_profile (And.intro z180K30ProfileV97D6U04M0323_profile (And.intro z180K30ProfileV97D6U04M0324_profile (And.intro z180K30ProfileV97D6U04M0325_profile (And.intro z180K30ProfileV97D6U04M0326_profile (And.intro z180K30ProfileV97D6U04M0327_profile (And.intro z180K30ProfileV97D6U04M0328_profile (And.intro z180K30ProfileV97D6U04M0329_profile (And.intro z180K30ProfileV97D6U04M0330_profile (And.intro z180K30ProfileV97D6U04M0331_profile (And.intro z180K30ProfileV97D6U04M0332_profile (And.intro z180K30ProfileV97D6U04M0333_profile (And.intro z180K30ProfileV97D6U04M0334_profile (And.intro z180K30ProfileV97D6U04M0335_profile (And.intro z180K30ProfileV97D6U04M0336_profile (And.intro z180K30ProfileV97D6U04M0337_profile (And.intro z180K30ProfileV97D6U04M0338_profile (z180K30ProfileV97D6U04M0339_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
