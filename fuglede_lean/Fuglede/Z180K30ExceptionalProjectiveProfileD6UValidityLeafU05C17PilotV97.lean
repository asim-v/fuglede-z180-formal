import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S083
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S084

/-! Bounded D6 U-validity leaf U05C17: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C17PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0340, z180K30ProfileV97D6U05M0341, z180K30ProfileV97D6U05M0342, z180K30ProfileV97D6U05M0343, z180K30ProfileV97D6U05M0344, z180K30ProfileV97D6U05M0345, z180K30ProfileV97D6U05M0346, z180K30ProfileV97D6U05M0347, z180K30ProfileV97D6U05M0348, z180K30ProfileV97D6U05M0349, z180K30ProfileV97D6U05M0350, z180K30ProfileV97D6U05M0351, z180K30ProfileV97D6U05M0352, z180K30ProfileV97D6U05M0353, z180K30ProfileV97D6U05M0354, z180K30ProfileV97D6U05M0355, z180K30ProfileV97D6U05M0356, z180K30ProfileV97D6U05M0357, z180K30ProfileV97D6U05M0358, z180K30ProfileV97D6U05M0359]

theorem z180_k30_projective_d6_u_validity_members_u05c17_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C17PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C17PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0340_profile (And.intro z180K30ProfileV97D6U05M0341_profile (And.intro z180K30ProfileV97D6U05M0342_profile (And.intro z180K30ProfileV97D6U05M0343_profile (And.intro z180K30ProfileV97D6U05M0344_profile (And.intro z180K30ProfileV97D6U05M0345_profile (And.intro z180K30ProfileV97D6U05M0346_profile (And.intro z180K30ProfileV97D6U05M0347_profile (And.intro z180K30ProfileV97D6U05M0348_profile (And.intro z180K30ProfileV97D6U05M0349_profile (And.intro z180K30ProfileV97D6U05M0350_profile (And.intro z180K30ProfileV97D6U05M0351_profile (And.intro z180K30ProfileV97D6U05M0352_profile (And.intro z180K30ProfileV97D6U05M0353_profile (And.intro z180K30ProfileV97D6U05M0354_profile (And.intro z180K30ProfileV97D6U05M0355_profile (And.intro z180K30ProfileV97D6U05M0356_profile (And.intro z180K30ProfileV97D6U05M0357_profile (And.intro z180K30ProfileV97D6U05M0358_profile (z180K30ProfileV97D6U05M0359_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
