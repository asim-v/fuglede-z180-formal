import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S087
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S088

/-! Bounded D6 U-validity leaf U05C21: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C21PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0420, z180K30ProfileV97D6U05M0421, z180K30ProfileV97D6U05M0422, z180K30ProfileV97D6U05M0423, z180K30ProfileV97D6U05M0424, z180K30ProfileV97D6U05M0425, z180K30ProfileV97D6U05M0426, z180K30ProfileV97D6U05M0427, z180K30ProfileV97D6U05M0428, z180K30ProfileV97D6U05M0429, z180K30ProfileV97D6U05M0430, z180K30ProfileV97D6U05M0431, z180K30ProfileV97D6U05M0432, z180K30ProfileV97D6U05M0433, z180K30ProfileV97D6U05M0434, z180K30ProfileV97D6U05M0435, z180K30ProfileV97D6U05M0436, z180K30ProfileV97D6U05M0437, z180K30ProfileV97D6U05M0438, z180K30ProfileV97D6U05M0439]

theorem z180_k30_projective_d6_u_validity_members_u05c21_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C21PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C21PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0420_profile (And.intro z180K30ProfileV97D6U05M0421_profile (And.intro z180K30ProfileV97D6U05M0422_profile (And.intro z180K30ProfileV97D6U05M0423_profile (And.intro z180K30ProfileV97D6U05M0424_profile (And.intro z180K30ProfileV97D6U05M0425_profile (And.intro z180K30ProfileV97D6U05M0426_profile (And.intro z180K30ProfileV97D6U05M0427_profile (And.intro z180K30ProfileV97D6U05M0428_profile (And.intro z180K30ProfileV97D6U05M0429_profile (And.intro z180K30ProfileV97D6U05M0430_profile (And.intro z180K30ProfileV97D6U05M0431_profile (And.intro z180K30ProfileV97D6U05M0432_profile (And.intro z180K30ProfileV97D6U05M0433_profile (And.intro z180K30ProfileV97D6U05M0434_profile (And.intro z180K30ProfileV97D6U05M0435_profile (And.intro z180K30ProfileV97D6U05M0436_profile (And.intro z180K30ProfileV97D6U05M0437_profile (And.intro z180K30ProfileV97D6U05M0438_profile (z180K30ProfileV97D6U05M0439_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
