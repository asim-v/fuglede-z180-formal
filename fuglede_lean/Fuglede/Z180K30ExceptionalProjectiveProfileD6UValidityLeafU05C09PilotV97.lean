import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S075
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S076

/-! Bounded D6 U-validity leaf U05C09: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C09PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0180, z180K30ProfileV97D6U05M0181, z180K30ProfileV97D6U05M0182, z180K30ProfileV97D6U05M0183, z180K30ProfileV97D6U05M0184, z180K30ProfileV97D6U05M0185, z180K30ProfileV97D6U05M0186, z180K30ProfileV97D6U05M0187, z180K30ProfileV97D6U05M0188, z180K30ProfileV97D6U05M0189, z180K30ProfileV97D6U05M0190, z180K30ProfileV97D6U05M0191, z180K30ProfileV97D6U05M0192, z180K30ProfileV97D6U05M0193, z180K30ProfileV97D6U05M0194, z180K30ProfileV97D6U05M0195, z180K30ProfileV97D6U05M0196, z180K30ProfileV97D6U05M0197, z180K30ProfileV97D6U05M0198, z180K30ProfileV97D6U05M0199]

theorem z180_k30_projective_d6_u_validity_members_u05c09_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C09PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C09PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0180_profile (And.intro z180K30ProfileV97D6U05M0181_profile (And.intro z180K30ProfileV97D6U05M0182_profile (And.intro z180K30ProfileV97D6U05M0183_profile (And.intro z180K30ProfileV97D6U05M0184_profile (And.intro z180K30ProfileV97D6U05M0185_profile (And.intro z180K30ProfileV97D6U05M0186_profile (And.intro z180K30ProfileV97D6U05M0187_profile (And.intro z180K30ProfileV97D6U05M0188_profile (And.intro z180K30ProfileV97D6U05M0189_profile (And.intro z180K30ProfileV97D6U05M0190_profile (And.intro z180K30ProfileV97D6U05M0191_profile (And.intro z180K30ProfileV97D6U05M0192_profile (And.intro z180K30ProfileV97D6U05M0193_profile (And.intro z180K30ProfileV97D6U05M0194_profile (And.intro z180K30ProfileV97D6U05M0195_profile (And.intro z180K30ProfileV97D6U05M0196_profile (And.intro z180K30ProfileV97D6U05M0197_profile (And.intro z180K30ProfileV97D6U05M0198_profile (z180K30ProfileV97D6U05M0199_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
