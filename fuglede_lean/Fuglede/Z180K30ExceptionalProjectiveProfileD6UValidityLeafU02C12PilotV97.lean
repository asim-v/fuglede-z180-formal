import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S032
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S033

/-! Bounded D6 U-validity leaf U02C12: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C12PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0240, z180K30ProfileV97D6U02M0241, z180K30ProfileV97D6U02M0242, z180K30ProfileV97D6U02M0243, z180K30ProfileV97D6U02M0244, z180K30ProfileV97D6U02M0245, z180K30ProfileV97D6U02M0246, z180K30ProfileV97D6U02M0247, z180K30ProfileV97D6U02M0248, z180K30ProfileV97D6U02M0249, z180K30ProfileV97D6U02M0250, z180K30ProfileV97D6U02M0251, z180K30ProfileV97D6U02M0252, z180K30ProfileV97D6U02M0253, z180K30ProfileV97D6U02M0254, z180K30ProfileV97D6U02M0255, z180K30ProfileV97D6U02M0256, z180K30ProfileV97D6U02M0257, z180K30ProfileV97D6U02M0258, z180K30ProfileV97D6U02M0259]

theorem z180_k30_projective_d6_u_validity_members_u02c12_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C12PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C12PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0240_profile (And.intro z180K30ProfileV97D6U02M0241_profile (And.intro z180K30ProfileV97D6U02M0242_profile (And.intro z180K30ProfileV97D6U02M0243_profile (And.intro z180K30ProfileV97D6U02M0244_profile (And.intro z180K30ProfileV97D6U02M0245_profile (And.intro z180K30ProfileV97D6U02M0246_profile (And.intro z180K30ProfileV97D6U02M0247_profile (And.intro z180K30ProfileV97D6U02M0248_profile (And.intro z180K30ProfileV97D6U02M0249_profile (And.intro z180K30ProfileV97D6U02M0250_profile (And.intro z180K30ProfileV97D6U02M0251_profile (And.intro z180K30ProfileV97D6U02M0252_profile (And.intro z180K30ProfileV97D6U02M0253_profile (And.intro z180K30ProfileV97D6U02M0254_profile (And.intro z180K30ProfileV97D6U02M0255_profile (And.intro z180K30ProfileV97D6U02M0256_profile (And.intro z180K30ProfileV97D6U02M0257_profile (And.intro z180K30ProfileV97D6U02M0258_profile (z180K30ProfileV97D6U02M0259_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
