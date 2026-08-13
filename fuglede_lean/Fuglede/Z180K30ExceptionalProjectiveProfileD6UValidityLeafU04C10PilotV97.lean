import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S056
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S057

/-! Bounded D6 U-validity leaf U04C10: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C10PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0200, z180K30ProfileV97D6U04M0201, z180K30ProfileV97D6U04M0202, z180K30ProfileV97D6U04M0203, z180K30ProfileV97D6U04M0204, z180K30ProfileV97D6U04M0205, z180K30ProfileV97D6U04M0206, z180K30ProfileV97D6U04M0207, z180K30ProfileV97D6U04M0208, z180K30ProfileV97D6U04M0209, z180K30ProfileV97D6U04M0210, z180K30ProfileV97D6U04M0211, z180K30ProfileV97D6U04M0212, z180K30ProfileV97D6U04M0213, z180K30ProfileV97D6U04M0214, z180K30ProfileV97D6U04M0215, z180K30ProfileV97D6U04M0216, z180K30ProfileV97D6U04M0217, z180K30ProfileV97D6U04M0218, z180K30ProfileV97D6U04M0219]

theorem z180_k30_projective_d6_u_validity_members_u04c10_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C10PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C10PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0200_profile (And.intro z180K30ProfileV97D6U04M0201_profile (And.intro z180K30ProfileV97D6U04M0202_profile (And.intro z180K30ProfileV97D6U04M0203_profile (And.intro z180K30ProfileV97D6U04M0204_profile (And.intro z180K30ProfileV97D6U04M0205_profile (And.intro z180K30ProfileV97D6U04M0206_profile (And.intro z180K30ProfileV97D6U04M0207_profile (And.intro z180K30ProfileV97D6U04M0208_profile (And.intro z180K30ProfileV97D6U04M0209_profile (And.intro z180K30ProfileV97D6U04M0210_profile (And.intro z180K30ProfileV97D6U04M0211_profile (And.intro z180K30ProfileV97D6U04M0212_profile (And.intro z180K30ProfileV97D6U04M0213_profile (And.intro z180K30ProfileV97D6U04M0214_profile (And.intro z180K30ProfileV97D6U04M0215_profile (And.intro z180K30ProfileV97D6U04M0216_profile (And.intro z180K30ProfileV97D6U04M0217_profile (And.intro z180K30ProfileV97D6U04M0218_profile (z180K30ProfileV97D6U04M0219_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
