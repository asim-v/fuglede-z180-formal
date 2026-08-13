import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S036
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S037

/-! Bounded D6 U-validity leaf U02C16: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C16PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0320, z180K30ProfileV97D6U02M0321, z180K30ProfileV97D6U02M0322, z180K30ProfileV97D6U02M0323, z180K30ProfileV97D6U02M0324, z180K30ProfileV97D6U02M0325, z180K30ProfileV97D6U02M0326, z180K30ProfileV97D6U02M0327, z180K30ProfileV97D6U02M0328, z180K30ProfileV97D6U02M0329, z180K30ProfileV97D6U02M0330, z180K30ProfileV97D6U02M0331, z180K30ProfileV97D6U02M0332, z180K30ProfileV97D6U02M0333, z180K30ProfileV97D6U02M0334, z180K30ProfileV97D6U02M0335, z180K30ProfileV97D6U02M0336, z180K30ProfileV97D6U02M0337, z180K30ProfileV97D6U02M0338, z180K30ProfileV97D6U02M0339]

theorem z180_k30_projective_d6_u_validity_members_u02c16_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C16PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C16PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0320_profile (And.intro z180K30ProfileV97D6U02M0321_profile (And.intro z180K30ProfileV97D6U02M0322_profile (And.intro z180K30ProfileV97D6U02M0323_profile (And.intro z180K30ProfileV97D6U02M0324_profile (And.intro z180K30ProfileV97D6U02M0325_profile (And.intro z180K30ProfileV97D6U02M0326_profile (And.intro z180K30ProfileV97D6U02M0327_profile (And.intro z180K30ProfileV97D6U02M0328_profile (And.intro z180K30ProfileV97D6U02M0329_profile (And.intro z180K30ProfileV97D6U02M0330_profile (And.intro z180K30ProfileV97D6U02M0331_profile (And.intro z180K30ProfileV97D6U02M0332_profile (And.intro z180K30ProfileV97D6U02M0333_profile (And.intro z180K30ProfileV97D6U02M0334_profile (And.intro z180K30ProfileV97D6U02M0335_profile (And.intro z180K30ProfileV97D6U02M0336_profile (And.intro z180K30ProfileV97D6U02M0337_profile (And.intro z180K30ProfileV97D6U02M0338_profile (z180K30ProfileV97D6U02M0339_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
