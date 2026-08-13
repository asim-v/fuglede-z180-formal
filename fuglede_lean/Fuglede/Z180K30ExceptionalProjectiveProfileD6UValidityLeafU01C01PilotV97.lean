import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S001
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S002

/-! Bounded D6 U-validity leaf U01C01: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C01PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0020, z180K30ProfileV97D6U01M0021, z180K30ProfileV97D6U01M0022, z180K30ProfileV97D6U01M0023, z180K30ProfileV97D6U01M0024, z180K30ProfileV97D6U01M0025, z180K30ProfileV97D6U01M0026, z180K30ProfileV97D6U01M0027, z180K30ProfileV97D6U01M0028, z180K30ProfileV97D6U01M0029, z180K30ProfileV97D6U01M0030, z180K30ProfileV97D6U01M0031, z180K30ProfileV97D6U01M0032, z180K30ProfileV97D6U01M0033, z180K30ProfileV97D6U01M0034, z180K30ProfileV97D6U01M0035, z180K30ProfileV97D6U01M0036, z180K30ProfileV97D6U01M0037, z180K30ProfileV97D6U01M0038, z180K30ProfileV97D6U01M0039]

theorem z180_k30_projective_d6_u_validity_members_u01c01_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C01PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C01PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0020_profile (And.intro z180K30ProfileV97D6U01M0021_profile (And.intro z180K30ProfileV97D6U01M0022_profile (And.intro z180K30ProfileV97D6U01M0023_profile (And.intro z180K30ProfileV97D6U01M0024_profile (And.intro z180K30ProfileV97D6U01M0025_profile (And.intro z180K30ProfileV97D6U01M0026_profile (And.intro z180K30ProfileV97D6U01M0027_profile (And.intro z180K30ProfileV97D6U01M0028_profile (And.intro z180K30ProfileV97D6U01M0029_profile (And.intro z180K30ProfileV97D6U01M0030_profile (And.intro z180K30ProfileV97D6U01M0031_profile (And.intro z180K30ProfileV97D6U01M0032_profile (And.intro z180K30ProfileV97D6U01M0033_profile (And.intro z180K30ProfileV97D6U01M0034_profile (And.intro z180K30ProfileV97D6U01M0035_profile (And.intro z180K30ProfileV97D6U01M0036_profile (And.intro z180K30ProfileV97D6U01M0037_profile (And.intro z180K30ProfileV97D6U01M0038_profile (z180K30ProfileV97D6U01M0039_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
