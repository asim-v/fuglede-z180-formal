import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S103
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S104

/-! Bounded D6 U-validity leaf U08C01: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU08C01PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U08M0020, z180K30ProfileV97D6U08M0021, z180K30ProfileV97D6U08M0022, z180K30ProfileV97D6U08M0023, z180K30ProfileV97D6U08M0024, z180K30ProfileV97D6U08M0025, z180K30ProfileV97D6U08M0026, z180K30ProfileV97D6U08M0027, z180K30ProfileV97D6U08M0028, z180K30ProfileV97D6U08M0029, z180K30ProfileV97D6U08M0030, z180K30ProfileV97D6U08M0031, z180K30ProfileV97D6U08M0032, z180K30ProfileV97D6U08M0033, z180K30ProfileV97D6U08M0034, z180K30ProfileV97D6U08M0035, z180K30ProfileV97D6U08M0036, z180K30ProfileV97D6U08M0037, z180K30ProfileV97D6U08M0038, z180K30ProfileV97D6U08M0039]

theorem z180_k30_projective_d6_u_validity_members_u08c01_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU08PilotV97)
      z180K30ProjectiveD6UValidityMembersU08C01PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU08C01PilotV97 z180K30ProjectiveD6UValidityProfileU08PilotV97
  exact And.intro z180K30ProfileV97D6U08M0020_profile (And.intro z180K30ProfileV97D6U08M0021_profile (And.intro z180K30ProfileV97D6U08M0022_profile (And.intro z180K30ProfileV97D6U08M0023_profile (And.intro z180K30ProfileV97D6U08M0024_profile (And.intro z180K30ProfileV97D6U08M0025_profile (And.intro z180K30ProfileV97D6U08M0026_profile (And.intro z180K30ProfileV97D6U08M0027_profile (And.intro z180K30ProfileV97D6U08M0028_profile (And.intro z180K30ProfileV97D6U08M0029_profile (And.intro z180K30ProfileV97D6U08M0030_profile (And.intro z180K30ProfileV97D6U08M0031_profile (And.intro z180K30ProfileV97D6U08M0032_profile (And.intro z180K30ProfileV97D6U08M0033_profile (And.intro z180K30ProfileV97D6U08M0034_profile (And.intro z180K30ProfileV97D6U08M0035_profile (And.intro z180K30ProfileV97D6U08M0036_profile (And.intro z180K30ProfileV97D6U08M0037_profile (And.intro z180K30ProfileV97D6U08M0038_profile (z180K30ProfileV97D6U08M0039_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
