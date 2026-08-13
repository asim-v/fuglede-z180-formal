import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S055
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S056

/-! Bounded D6 U-validity leaf U04C09: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C09PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0180, z180K30ProfileV97D6U04M0181, z180K30ProfileV97D6U04M0182, z180K30ProfileV97D6U04M0183, z180K30ProfileV97D6U04M0184, z180K30ProfileV97D6U04M0185, z180K30ProfileV97D6U04M0186, z180K30ProfileV97D6U04M0187, z180K30ProfileV97D6U04M0188, z180K30ProfileV97D6U04M0189, z180K30ProfileV97D6U04M0190, z180K30ProfileV97D6U04M0191, z180K30ProfileV97D6U04M0192, z180K30ProfileV97D6U04M0193, z180K30ProfileV97D6U04M0194, z180K30ProfileV97D6U04M0195, z180K30ProfileV97D6U04M0196, z180K30ProfileV97D6U04M0197, z180K30ProfileV97D6U04M0198, z180K30ProfileV97D6U04M0199]

theorem z180_k30_projective_d6_u_validity_members_u04c09_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C09PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C09PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0180_profile (And.intro z180K30ProfileV97D6U04M0181_profile (And.intro z180K30ProfileV97D6U04M0182_profile (And.intro z180K30ProfileV97D6U04M0183_profile (And.intro z180K30ProfileV97D6U04M0184_profile (And.intro z180K30ProfileV97D6U04M0185_profile (And.intro z180K30ProfileV97D6U04M0186_profile (And.intro z180K30ProfileV97D6U04M0187_profile (And.intro z180K30ProfileV97D6U04M0188_profile (And.intro z180K30ProfileV97D6U04M0189_profile (And.intro z180K30ProfileV97D6U04M0190_profile (And.intro z180K30ProfileV97D6U04M0191_profile (And.intro z180K30ProfileV97D6U04M0192_profile (And.intro z180K30ProfileV97D6U04M0193_profile (And.intro z180K30ProfileV97D6U04M0194_profile (And.intro z180K30ProfileV97D6U04M0195_profile (And.intro z180K30ProfileV97D6U04M0196_profile (And.intro z180K30ProfileV97D6U04M0197_profile (And.intro z180K30ProfileV97D6U04M0198_profile (z180K30ProfileV97D6U04M0199_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
