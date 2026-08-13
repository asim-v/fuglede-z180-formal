import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S021
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S022

/-! Bounded D6 U-validity leaf U02C01: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C01PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0020, z180K30ProfileV97D6U02M0021, z180K30ProfileV97D6U02M0022, z180K30ProfileV97D6U02M0023, z180K30ProfileV97D6U02M0024, z180K30ProfileV97D6U02M0025, z180K30ProfileV97D6U02M0026, z180K30ProfileV97D6U02M0027, z180K30ProfileV97D6U02M0028, z180K30ProfileV97D6U02M0029, z180K30ProfileV97D6U02M0030, z180K30ProfileV97D6U02M0031, z180K30ProfileV97D6U02M0032, z180K30ProfileV97D6U02M0033, z180K30ProfileV97D6U02M0034, z180K30ProfileV97D6U02M0035, z180K30ProfileV97D6U02M0036, z180K30ProfileV97D6U02M0037, z180K30ProfileV97D6U02M0038, z180K30ProfileV97D6U02M0039]

theorem z180_k30_projective_d6_u_validity_members_u02c01_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C01PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C01PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0020_profile (And.intro z180K30ProfileV97D6U02M0021_profile (And.intro z180K30ProfileV97D6U02M0022_profile (And.intro z180K30ProfileV97D6U02M0023_profile (And.intro z180K30ProfileV97D6U02M0024_profile (And.intro z180K30ProfileV97D6U02M0025_profile (And.intro z180K30ProfileV97D6U02M0026_profile (And.intro z180K30ProfileV97D6U02M0027_profile (And.intro z180K30ProfileV97D6U02M0028_profile (And.intro z180K30ProfileV97D6U02M0029_profile (And.intro z180K30ProfileV97D6U02M0030_profile (And.intro z180K30ProfileV97D6U02M0031_profile (And.intro z180K30ProfileV97D6U02M0032_profile (And.intro z180K30ProfileV97D6U02M0033_profile (And.intro z180K30ProfileV97D6U02M0034_profile (And.intro z180K30ProfileV97D6U02M0035_profile (And.intro z180K30ProfileV97D6U02M0036_profile (And.intro z180K30ProfileV97D6U02M0037_profile (And.intro z180K30ProfileV97D6U02M0038_profile (z180K30ProfileV97D6U02M0039_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
