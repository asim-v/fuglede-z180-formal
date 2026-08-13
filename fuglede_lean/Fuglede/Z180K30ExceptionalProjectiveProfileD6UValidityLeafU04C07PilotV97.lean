import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S053
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S054

/-! Bounded D6 U-validity leaf U04C07: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C07PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0140, z180K30ProfileV97D6U04M0141, z180K30ProfileV97D6U04M0142, z180K30ProfileV97D6U04M0143, z180K30ProfileV97D6U04M0144, z180K30ProfileV97D6U04M0145, z180K30ProfileV97D6U04M0146, z180K30ProfileV97D6U04M0147, z180K30ProfileV97D6U04M0148, z180K30ProfileV97D6U04M0149, z180K30ProfileV97D6U04M0150, z180K30ProfileV97D6U04M0151, z180K30ProfileV97D6U04M0152, z180K30ProfileV97D6U04M0153, z180K30ProfileV97D6U04M0154, z180K30ProfileV97D6U04M0155, z180K30ProfileV97D6U04M0156, z180K30ProfileV97D6U04M0157, z180K30ProfileV97D6U04M0158, z180K30ProfileV97D6U04M0159]

theorem z180_k30_projective_d6_u_validity_members_u04c07_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C07PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C07PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0140_profile (And.intro z180K30ProfileV97D6U04M0141_profile (And.intro z180K30ProfileV97D6U04M0142_profile (And.intro z180K30ProfileV97D6U04M0143_profile (And.intro z180K30ProfileV97D6U04M0144_profile (And.intro z180K30ProfileV97D6U04M0145_profile (And.intro z180K30ProfileV97D6U04M0146_profile (And.intro z180K30ProfileV97D6U04M0147_profile (And.intro z180K30ProfileV97D6U04M0148_profile (And.intro z180K30ProfileV97D6U04M0149_profile (And.intro z180K30ProfileV97D6U04M0150_profile (And.intro z180K30ProfileV97D6U04M0151_profile (And.intro z180K30ProfileV97D6U04M0152_profile (And.intro z180K30ProfileV97D6U04M0153_profile (And.intro z180K30ProfileV97D6U04M0154_profile (And.intro z180K30ProfileV97D6U04M0155_profile (And.intro z180K30ProfileV97D6U04M0156_profile (And.intro z180K30ProfileV97D6U04M0157_profile (And.intro z180K30ProfileV97D6U04M0158_profile (z180K30ProfileV97D6U04M0159_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
