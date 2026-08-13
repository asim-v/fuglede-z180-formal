import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S063
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S064

/-! Bounded D6 U-validity leaf U04C17: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C17PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0340, z180K30ProfileV97D6U04M0341, z180K30ProfileV97D6U04M0342, z180K30ProfileV97D6U04M0343, z180K30ProfileV97D6U04M0344, z180K30ProfileV97D6U04M0345, z180K30ProfileV97D6U04M0346, z180K30ProfileV97D6U04M0347, z180K30ProfileV97D6U04M0348, z180K30ProfileV97D6U04M0349, z180K30ProfileV97D6U04M0350, z180K30ProfileV97D6U04M0351, z180K30ProfileV97D6U04M0352, z180K30ProfileV97D6U04M0353, z180K30ProfileV97D6U04M0354, z180K30ProfileV97D6U04M0355, z180K30ProfileV97D6U04M0356, z180K30ProfileV97D6U04M0357, z180K30ProfileV97D6U04M0358, z180K30ProfileV97D6U04M0359]

theorem z180_k30_projective_d6_u_validity_members_u04c17_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C17PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C17PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0340_profile (And.intro z180K30ProfileV97D6U04M0341_profile (And.intro z180K30ProfileV97D6U04M0342_profile (And.intro z180K30ProfileV97D6U04M0343_profile (And.intro z180K30ProfileV97D6U04M0344_profile (And.intro z180K30ProfileV97D6U04M0345_profile (And.intro z180K30ProfileV97D6U04M0346_profile (And.intro z180K30ProfileV97D6U04M0347_profile (And.intro z180K30ProfileV97D6U04M0348_profile (And.intro z180K30ProfileV97D6U04M0349_profile (And.intro z180K30ProfileV97D6U04M0350_profile (And.intro z180K30ProfileV97D6U04M0351_profile (And.intro z180K30ProfileV97D6U04M0352_profile (And.intro z180K30ProfileV97D6U04M0353_profile (And.intro z180K30ProfileV97D6U04M0354_profile (And.intro z180K30ProfileV97D6U04M0355_profile (And.intro z180K30ProfileV97D6U04M0356_profile (And.intro z180K30ProfileV97D6U04M0357_profile (And.intro z180K30ProfileV97D6U04M0358_profile (z180K30ProfileV97D6U04M0359_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
