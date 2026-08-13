import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S099
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S100

/-! Bounded D6 U-validity leaf U07C07: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07C07PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U07M0140, z180K30ProfileV97D6U07M0141, z180K30ProfileV97D6U07M0142, z180K30ProfileV97D6U07M0143, z180K30ProfileV97D6U07M0144, z180K30ProfileV97D6U07M0145, z180K30ProfileV97D6U07M0146, z180K30ProfileV97D6U07M0147, z180K30ProfileV97D6U07M0148, z180K30ProfileV97D6U07M0149, z180K30ProfileV97D6U07M0150, z180K30ProfileV97D6U07M0151, z180K30ProfileV97D6U07M0152, z180K30ProfileV97D6U07M0153, z180K30ProfileV97D6U07M0154, z180K30ProfileV97D6U07M0155, z180K30ProfileV97D6U07M0156, z180K30ProfileV97D6U07M0157, z180K30ProfileV97D6U07M0158, z180K30ProfileV97D6U07M0159]

theorem z180_k30_projective_d6_u_validity_members_u07c07_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07C07PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07C07PilotV97 z180K30ProjectiveD6UValidityProfileU07PilotV97
  exact And.intro z180K30ProfileV97D6U07M0140_profile (And.intro z180K30ProfileV97D6U07M0141_profile (And.intro z180K30ProfileV97D6U07M0142_profile (And.intro z180K30ProfileV97D6U07M0143_profile (And.intro z180K30ProfileV97D6U07M0144_profile (And.intro z180K30ProfileV97D6U07M0145_profile (And.intro z180K30ProfileV97D6U07M0146_profile (And.intro z180K30ProfileV97D6U07M0147_profile (And.intro z180K30ProfileV97D6U07M0148_profile (And.intro z180K30ProfileV97D6U07M0149_profile (And.intro z180K30ProfileV97D6U07M0150_profile (And.intro z180K30ProfileV97D6U07M0151_profile (And.intro z180K30ProfileV97D6U07M0152_profile (And.intro z180K30ProfileV97D6U07M0153_profile (And.intro z180K30ProfileV97D6U07M0154_profile (And.intro z180K30ProfileV97D6U07M0155_profile (And.intro z180K30ProfileV97D6U07M0156_profile (And.intro z180K30ProfileV97D6U07M0157_profile (And.intro z180K30ProfileV97D6U07M0158_profile (z180K30ProfileV97D6U07M0159_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
