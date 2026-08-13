import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S000

/-! Bounded D6 U-validity leaf U00C00: 1 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU00C00PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U00M0000]

theorem z180_k30_projective_d6_u_validity_members_u00c00_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU00PilotV97)
      z180K30ProjectiveD6UValidityMembersU00C00PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU00C00PilotV97 z180K30ProjectiveD6UValidityProfileU00PilotV97
  exact z180K30ProfileV97D6U00M0000_profile

end Fuglede.Z180K30ExceptionalRawV2
