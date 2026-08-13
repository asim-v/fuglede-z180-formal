import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S009
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S010

/-! Bounded D6 U-validity leaf U01C09: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C09PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0180, z180K30ProfileV97D6U01M0181, z180K30ProfileV97D6U01M0182, z180K30ProfileV97D6U01M0183, z180K30ProfileV97D6U01M0184, z180K30ProfileV97D6U01M0185, z180K30ProfileV97D6U01M0186, z180K30ProfileV97D6U01M0187, z180K30ProfileV97D6U01M0188, z180K30ProfileV97D6U01M0189, z180K30ProfileV97D6U01M0190, z180K30ProfileV97D6U01M0191, z180K30ProfileV97D6U01M0192, z180K30ProfileV97D6U01M0193, z180K30ProfileV97D6U01M0194, z180K30ProfileV97D6U01M0195, z180K30ProfileV97D6U01M0196, z180K30ProfileV97D6U01M0197, z180K30ProfileV97D6U01M0198, z180K30ProfileV97D6U01M0199]

theorem z180_k30_projective_d6_u_validity_members_u01c09_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C09PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C09PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0180_profile (And.intro z180K30ProfileV97D6U01M0181_profile (And.intro z180K30ProfileV97D6U01M0182_profile (And.intro z180K30ProfileV97D6U01M0183_profile (And.intro z180K30ProfileV97D6U01M0184_profile (And.intro z180K30ProfileV97D6U01M0185_profile (And.intro z180K30ProfileV97D6U01M0186_profile (And.intro z180K30ProfileV97D6U01M0187_profile (And.intro z180K30ProfileV97D6U01M0188_profile (And.intro z180K30ProfileV97D6U01M0189_profile (And.intro z180K30ProfileV97D6U01M0190_profile (And.intro z180K30ProfileV97D6U01M0191_profile (And.intro z180K30ProfileV97D6U01M0192_profile (And.intro z180K30ProfileV97D6U01M0193_profile (And.intro z180K30ProfileV97D6U01M0194_profile (And.intro z180K30ProfileV97D6U01M0195_profile (And.intro z180K30ProfileV97D6U01M0196_profile (And.intro z180K30ProfileV97D6U01M0197_profile (And.intro z180K30ProfileV97D6U01M0198_profile (z180K30ProfileV97D6U01M0199_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
