import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S113

/-! Bounded D6 U-validity leaf U08C11: 5 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU08C11PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U08M0220, z180K30ProfileV97D6U08M0221, z180K30ProfileV97D6U08M0222, z180K30ProfileV97D6U08M0223, z180K30ProfileV97D6U08M0224]

theorem z180_k30_projective_d6_u_validity_members_u08c11_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU08PilotV97)
      z180K30ProjectiveD6UValidityMembersU08C11PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU08C11PilotV97 z180K30ProjectiveD6UValidityProfileU08PilotV97
  exact And.intro z180K30ProfileV97D6U08M0220_profile (And.intro z180K30ProfileV97D6U08M0221_profile (And.intro z180K30ProfileV97D6U08M0222_profile (And.intro z180K30ProfileV97D6U08M0223_profile (z180K30ProfileV97D6U08M0224_profile))))

end Fuglede.Z180K30ExceptionalRawV2
