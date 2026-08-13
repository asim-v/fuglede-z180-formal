import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S057
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S058

/-! Bounded D6 U-validity leaf U04C11: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C11PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0220, z180K30ProfileV97D6U04M0221, z180K30ProfileV97D6U04M0222, z180K30ProfileV97D6U04M0223, z180K30ProfileV97D6U04M0224, z180K30ProfileV97D6U04M0225, z180K30ProfileV97D6U04M0226, z180K30ProfileV97D6U04M0227, z180K30ProfileV97D6U04M0228, z180K30ProfileV97D6U04M0229, z180K30ProfileV97D6U04M0230, z180K30ProfileV97D6U04M0231, z180K30ProfileV97D6U04M0232, z180K30ProfileV97D6U04M0233, z180K30ProfileV97D6U04M0234, z180K30ProfileV97D6U04M0235, z180K30ProfileV97D6U04M0236, z180K30ProfileV97D6U04M0237, z180K30ProfileV97D6U04M0238, z180K30ProfileV97D6U04M0239]

theorem z180_k30_projective_d6_u_validity_members_u04c11_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C11PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C11PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0220_profile (And.intro z180K30ProfileV97D6U04M0221_profile (And.intro z180K30ProfileV97D6U04M0222_profile (And.intro z180K30ProfileV97D6U04M0223_profile (And.intro z180K30ProfileV97D6U04M0224_profile (And.intro z180K30ProfileV97D6U04M0225_profile (And.intro z180K30ProfileV97D6U04M0226_profile (And.intro z180K30ProfileV97D6U04M0227_profile (And.intro z180K30ProfileV97D6U04M0228_profile (And.intro z180K30ProfileV97D6U04M0229_profile (And.intro z180K30ProfileV97D6U04M0230_profile (And.intro z180K30ProfileV97D6U04M0231_profile (And.intro z180K30ProfileV97D6U04M0232_profile (And.intro z180K30ProfileV97D6U04M0233_profile (And.intro z180K30ProfileV97D6U04M0234_profile (And.intro z180K30ProfileV97D6U04M0235_profile (And.intro z180K30ProfileV97D6U04M0236_profile (And.intro z180K30ProfileV97D6U04M0237_profile (And.intro z180K30ProfileV97D6U04M0238_profile (z180K30ProfileV97D6U04M0239_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
