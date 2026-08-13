import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S031
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S032

/-! Bounded D6 U-validity leaf U02C11: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C11PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0220, z180K30ProfileV97D6U02M0221, z180K30ProfileV97D6U02M0222, z180K30ProfileV97D6U02M0223, z180K30ProfileV97D6U02M0224, z180K30ProfileV97D6U02M0225, z180K30ProfileV97D6U02M0226, z180K30ProfileV97D6U02M0227, z180K30ProfileV97D6U02M0228, z180K30ProfileV97D6U02M0229, z180K30ProfileV97D6U02M0230, z180K30ProfileV97D6U02M0231, z180K30ProfileV97D6U02M0232, z180K30ProfileV97D6U02M0233, z180K30ProfileV97D6U02M0234, z180K30ProfileV97D6U02M0235, z180K30ProfileV97D6U02M0236, z180K30ProfileV97D6U02M0237, z180K30ProfileV97D6U02M0238, z180K30ProfileV97D6U02M0239]

theorem z180_k30_projective_d6_u_validity_members_u02c11_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C11PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C11PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0220_profile (And.intro z180K30ProfileV97D6U02M0221_profile (And.intro z180K30ProfileV97D6U02M0222_profile (And.intro z180K30ProfileV97D6U02M0223_profile (And.intro z180K30ProfileV97D6U02M0224_profile (And.intro z180K30ProfileV97D6U02M0225_profile (And.intro z180K30ProfileV97D6U02M0226_profile (And.intro z180K30ProfileV97D6U02M0227_profile (And.intro z180K30ProfileV97D6U02M0228_profile (And.intro z180K30ProfileV97D6U02M0229_profile (And.intro z180K30ProfileV97D6U02M0230_profile (And.intro z180K30ProfileV97D6U02M0231_profile (And.intro z180K30ProfileV97D6U02M0232_profile (And.intro z180K30ProfileV97D6U02M0233_profile (And.intro z180K30ProfileV97D6U02M0234_profile (And.intro z180K30ProfileV97D6U02M0235_profile (And.intro z180K30ProfileV97D6U02M0236_profile (And.intro z180K30ProfileV97D6U02M0237_profile (And.intro z180K30ProfileV97D6U02M0238_profile (z180K30ProfileV97D6U02M0239_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
