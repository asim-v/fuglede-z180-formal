import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S114
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S115

/-! Bounded D6 U-validity leaf U09C01: 16 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU09C01PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U09M0020, z180K30ProfileV97D6U09M0021, z180K30ProfileV97D6U09M0022, z180K30ProfileV97D6U09M0023, z180K30ProfileV97D6U09M0024, z180K30ProfileV97D6U09M0025, z180K30ProfileV97D6U09M0026, z180K30ProfileV97D6U09M0027, z180K30ProfileV97D6U09M0028, z180K30ProfileV97D6U09M0029, z180K30ProfileV97D6U09M0030, z180K30ProfileV97D6U09M0031, z180K30ProfileV97D6U09M0032, z180K30ProfileV97D6U09M0033, z180K30ProfileV97D6U09M0034, z180K30ProfileV97D6U09M0035]

theorem z180_k30_projective_d6_u_validity_members_u09c01_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU09PilotV97)
      z180K30ProjectiveD6UValidityMembersU09C01PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU09C01PilotV97 z180K30ProjectiveD6UValidityProfileU09PilotV97
  exact And.intro z180K30ProfileV97D6U09M0020_profile (And.intro z180K30ProfileV97D6U09M0021_profile (And.intro z180K30ProfileV97D6U09M0022_profile (And.intro z180K30ProfileV97D6U09M0023_profile (And.intro z180K30ProfileV97D6U09M0024_profile (And.intro z180K30ProfileV97D6U09M0025_profile (And.intro z180K30ProfileV97D6U09M0026_profile (And.intro z180K30ProfileV97D6U09M0027_profile (And.intro z180K30ProfileV97D6U09M0028_profile (And.intro z180K30ProfileV97D6U09M0029_profile (And.intro z180K30ProfileV97D6U09M0030_profile (And.intro z180K30ProfileV97D6U09M0031_profile (And.intro z180K30ProfileV97D6U09M0032_profile (And.intro z180K30ProfileV97D6U09M0033_profile (And.intro z180K30ProfileV97D6U09M0034_profile (z180K30ProfileV97D6U09M0035_profile)))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
