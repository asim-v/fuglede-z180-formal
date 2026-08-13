import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S012
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S013

/-! Bounded D6 U-validity leaf U01C12: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C12PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0240, z180K30ProfileV97D6U01M0241, z180K30ProfileV97D6U01M0242, z180K30ProfileV97D6U01M0243, z180K30ProfileV97D6U01M0244, z180K30ProfileV97D6U01M0245, z180K30ProfileV97D6U01M0246, z180K30ProfileV97D6U01M0247, z180K30ProfileV97D6U01M0248, z180K30ProfileV97D6U01M0249, z180K30ProfileV97D6U01M0250, z180K30ProfileV97D6U01M0251, z180K30ProfileV97D6U01M0252, z180K30ProfileV97D6U01M0253, z180K30ProfileV97D6U01M0254, z180K30ProfileV97D6U01M0255, z180K30ProfileV97D6U01M0256, z180K30ProfileV97D6U01M0257, z180K30ProfileV97D6U01M0258, z180K30ProfileV97D6U01M0259]

theorem z180_k30_projective_d6_u_validity_members_u01c12_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C12PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C12PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0240_profile (And.intro z180K30ProfileV97D6U01M0241_profile (And.intro z180K30ProfileV97D6U01M0242_profile (And.intro z180K30ProfileV97D6U01M0243_profile (And.intro z180K30ProfileV97D6U01M0244_profile (And.intro z180K30ProfileV97D6U01M0245_profile (And.intro z180K30ProfileV97D6U01M0246_profile (And.intro z180K30ProfileV97D6U01M0247_profile (And.intro z180K30ProfileV97D6U01M0248_profile (And.intro z180K30ProfileV97D6U01M0249_profile (And.intro z180K30ProfileV97D6U01M0250_profile (And.intro z180K30ProfileV97D6U01M0251_profile (And.intro z180K30ProfileV97D6U01M0252_profile (And.intro z180K30ProfileV97D6U01M0253_profile (And.intro z180K30ProfileV97D6U01M0254_profile (And.intro z180K30ProfileV97D6U01M0255_profile (And.intro z180K30ProfileV97D6U01M0256_profile (And.intro z180K30ProfileV97D6U01M0257_profile (And.intro z180K30ProfileV97D6U01M0258_profile (z180K30ProfileV97D6U01M0259_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
