import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S013
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S014

/-! Bounded D6 U-validity leaf U01C13: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C13PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0260, z180K30ProfileV97D6U01M0261, z180K30ProfileV97D6U01M0262, z180K30ProfileV97D6U01M0263, z180K30ProfileV97D6U01M0264, z180K30ProfileV97D6U01M0265, z180K30ProfileV97D6U01M0266, z180K30ProfileV97D6U01M0267, z180K30ProfileV97D6U01M0268, z180K30ProfileV97D6U01M0269, z180K30ProfileV97D6U01M0270, z180K30ProfileV97D6U01M0271, z180K30ProfileV97D6U01M0272, z180K30ProfileV97D6U01M0273, z180K30ProfileV97D6U01M0274, z180K30ProfileV97D6U01M0275, z180K30ProfileV97D6U01M0276, z180K30ProfileV97D6U01M0277, z180K30ProfileV97D6U01M0278, z180K30ProfileV97D6U01M0279]

theorem z180_k30_projective_d6_u_validity_members_u01c13_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C13PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C13PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0260_profile (And.intro z180K30ProfileV97D6U01M0261_profile (And.intro z180K30ProfileV97D6U01M0262_profile (And.intro z180K30ProfileV97D6U01M0263_profile (And.intro z180K30ProfileV97D6U01M0264_profile (And.intro z180K30ProfileV97D6U01M0265_profile (And.intro z180K30ProfileV97D6U01M0266_profile (And.intro z180K30ProfileV97D6U01M0267_profile (And.intro z180K30ProfileV97D6U01M0268_profile (And.intro z180K30ProfileV97D6U01M0269_profile (And.intro z180K30ProfileV97D6U01M0270_profile (And.intro z180K30ProfileV97D6U01M0271_profile (And.intro z180K30ProfileV97D6U01M0272_profile (And.intro z180K30ProfileV97D6U01M0273_profile (And.intro z180K30ProfileV97D6U01M0274_profile (And.intro z180K30ProfileV97D6U01M0275_profile (And.intro z180K30ProfileV97D6U01M0276_profile (And.intro z180K30ProfileV97D6U01M0277_profile (And.intro z180K30ProfileV97D6U01M0278_profile (z180K30ProfileV97D6U01M0279_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
