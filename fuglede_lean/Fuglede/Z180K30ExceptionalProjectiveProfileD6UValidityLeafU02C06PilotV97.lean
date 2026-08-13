import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S026
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S027

/-! Bounded D6 U-validity leaf U02C06: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C06PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0120, z180K30ProfileV97D6U02M0121, z180K30ProfileV97D6U02M0122, z180K30ProfileV97D6U02M0123, z180K30ProfileV97D6U02M0124, z180K30ProfileV97D6U02M0125, z180K30ProfileV97D6U02M0126, z180K30ProfileV97D6U02M0127, z180K30ProfileV97D6U02M0128, z180K30ProfileV97D6U02M0129, z180K30ProfileV97D6U02M0130, z180K30ProfileV97D6U02M0131, z180K30ProfileV97D6U02M0132, z180K30ProfileV97D6U02M0133, z180K30ProfileV97D6U02M0134, z180K30ProfileV97D6U02M0135, z180K30ProfileV97D6U02M0136, z180K30ProfileV97D6U02M0137, z180K30ProfileV97D6U02M0138, z180K30ProfileV97D6U02M0139]

theorem z180_k30_projective_d6_u_validity_members_u02c06_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C06PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C06PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0120_profile (And.intro z180K30ProfileV97D6U02M0121_profile (And.intro z180K30ProfileV97D6U02M0122_profile (And.intro z180K30ProfileV97D6U02M0123_profile (And.intro z180K30ProfileV97D6U02M0124_profile (And.intro z180K30ProfileV97D6U02M0125_profile (And.intro z180K30ProfileV97D6U02M0126_profile (And.intro z180K30ProfileV97D6U02M0127_profile (And.intro z180K30ProfileV97D6U02M0128_profile (And.intro z180K30ProfileV97D6U02M0129_profile (And.intro z180K30ProfileV97D6U02M0130_profile (And.intro z180K30ProfileV97D6U02M0131_profile (And.intro z180K30ProfileV97D6U02M0132_profile (And.intro z180K30ProfileV97D6U02M0133_profile (And.intro z180K30ProfileV97D6U02M0134_profile (And.intro z180K30ProfileV97D6U02M0135_profile (And.intro z180K30ProfileV97D6U02M0136_profile (And.intro z180K30ProfileV97D6U02M0137_profile (And.intro z180K30ProfileV97D6U02M0138_profile (z180K30ProfileV97D6U02M0139_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
