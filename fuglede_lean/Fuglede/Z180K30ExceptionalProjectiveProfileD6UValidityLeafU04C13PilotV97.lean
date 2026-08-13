import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S059
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S060

/-! Bounded D6 U-validity leaf U04C13: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C13PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0260, z180K30ProfileV97D6U04M0261, z180K30ProfileV97D6U04M0262, z180K30ProfileV97D6U04M0263, z180K30ProfileV97D6U04M0264, z180K30ProfileV97D6U04M0265, z180K30ProfileV97D6U04M0266, z180K30ProfileV97D6U04M0267, z180K30ProfileV97D6U04M0268, z180K30ProfileV97D6U04M0269, z180K30ProfileV97D6U04M0270, z180K30ProfileV97D6U04M0271, z180K30ProfileV97D6U04M0272, z180K30ProfileV97D6U04M0273, z180K30ProfileV97D6U04M0274, z180K30ProfileV97D6U04M0275, z180K30ProfileV97D6U04M0276, z180K30ProfileV97D6U04M0277, z180K30ProfileV97D6U04M0278, z180K30ProfileV97D6U04M0279]

theorem z180_k30_projective_d6_u_validity_members_u04c13_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C13PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C13PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0260_profile (And.intro z180K30ProfileV97D6U04M0261_profile (And.intro z180K30ProfileV97D6U04M0262_profile (And.intro z180K30ProfileV97D6U04M0263_profile (And.intro z180K30ProfileV97D6U04M0264_profile (And.intro z180K30ProfileV97D6U04M0265_profile (And.intro z180K30ProfileV97D6U04M0266_profile (And.intro z180K30ProfileV97D6U04M0267_profile (And.intro z180K30ProfileV97D6U04M0268_profile (And.intro z180K30ProfileV97D6U04M0269_profile (And.intro z180K30ProfileV97D6U04M0270_profile (And.intro z180K30ProfileV97D6U04M0271_profile (And.intro z180K30ProfileV97D6U04M0272_profile (And.intro z180K30ProfileV97D6U04M0273_profile (And.intro z180K30ProfileV97D6U04M0274_profile (And.intro z180K30ProfileV97D6U04M0275_profile (And.intro z180K30ProfileV97D6U04M0276_profile (And.intro z180K30ProfileV97D6U04M0277_profile (And.intro z180K30ProfileV97D6U04M0278_profile (z180K30ProfileV97D6U04M0279_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
