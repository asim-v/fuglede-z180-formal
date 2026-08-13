import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S112
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S113

/-! Bounded D6 U-validity leaf U08C10: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU08C10PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U08M0200, z180K30ProfileV97D6U08M0201, z180K30ProfileV97D6U08M0202, z180K30ProfileV97D6U08M0203, z180K30ProfileV97D6U08M0204, z180K30ProfileV97D6U08M0205, z180K30ProfileV97D6U08M0206, z180K30ProfileV97D6U08M0207, z180K30ProfileV97D6U08M0208, z180K30ProfileV97D6U08M0209, z180K30ProfileV97D6U08M0210, z180K30ProfileV97D6U08M0211, z180K30ProfileV97D6U08M0212, z180K30ProfileV97D6U08M0213, z180K30ProfileV97D6U08M0214, z180K30ProfileV97D6U08M0215, z180K30ProfileV97D6U08M0216, z180K30ProfileV97D6U08M0217, z180K30ProfileV97D6U08M0218, z180K30ProfileV97D6U08M0219]

theorem z180_k30_projective_d6_u_validity_members_u08c10_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU08PilotV97)
      z180K30ProjectiveD6UValidityMembersU08C10PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU08C10PilotV97 z180K30ProjectiveD6UValidityProfileU08PilotV97
  exact And.intro z180K30ProfileV97D6U08M0200_profile (And.intro z180K30ProfileV97D6U08M0201_profile (And.intro z180K30ProfileV97D6U08M0202_profile (And.intro z180K30ProfileV97D6U08M0203_profile (And.intro z180K30ProfileV97D6U08M0204_profile (And.intro z180K30ProfileV97D6U08M0205_profile (And.intro z180K30ProfileV97D6U08M0206_profile (And.intro z180K30ProfileV97D6U08M0207_profile (And.intro z180K30ProfileV97D6U08M0208_profile (And.intro z180K30ProfileV97D6U08M0209_profile (And.intro z180K30ProfileV97D6U08M0210_profile (And.intro z180K30ProfileV97D6U08M0211_profile (And.intro z180K30ProfileV97D6U08M0212_profile (And.intro z180K30ProfileV97D6U08M0213_profile (And.intro z180K30ProfileV97D6U08M0214_profile (And.intro z180K30ProfileV97D6U08M0215_profile (And.intro z180K30ProfileV97D6U08M0216_profile (And.intro z180K30ProfileV97D6U08M0217_profile (And.intro z180K30ProfileV97D6U08M0218_profile (z180K30ProfileV97D6U08M0219_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
