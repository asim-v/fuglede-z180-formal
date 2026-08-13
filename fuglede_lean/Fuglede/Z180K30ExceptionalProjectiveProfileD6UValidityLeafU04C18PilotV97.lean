import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S064
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S065

/-! Bounded D6 U-validity leaf U04C18: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU04C18PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U04M0360, z180K30ProfileV97D6U04M0361, z180K30ProfileV97D6U04M0362, z180K30ProfileV97D6U04M0363, z180K30ProfileV97D6U04M0364, z180K30ProfileV97D6U04M0365, z180K30ProfileV97D6U04M0366, z180K30ProfileV97D6U04M0367, z180K30ProfileV97D6U04M0368, z180K30ProfileV97D6U04M0369, z180K30ProfileV97D6U04M0370, z180K30ProfileV97D6U04M0371, z180K30ProfileV97D6U04M0372, z180K30ProfileV97D6U04M0373, z180K30ProfileV97D6U04M0374, z180K30ProfileV97D6U04M0375, z180K30ProfileV97D6U04M0376, z180K30ProfileV97D6U04M0377, z180K30ProfileV97D6U04M0378, z180K30ProfileV97D6U04M0379]

theorem z180_k30_projective_d6_u_validity_members_u04c18_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU04PilotV97)
      z180K30ProjectiveD6UValidityMembersU04C18PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU04C18PilotV97 z180K30ProjectiveD6UValidityProfileU04PilotV97
  exact And.intro z180K30ProfileV97D6U04M0360_profile (And.intro z180K30ProfileV97D6U04M0361_profile (And.intro z180K30ProfileV97D6U04M0362_profile (And.intro z180K30ProfileV97D6U04M0363_profile (And.intro z180K30ProfileV97D6U04M0364_profile (And.intro z180K30ProfileV97D6U04M0365_profile (And.intro z180K30ProfileV97D6U04M0366_profile (And.intro z180K30ProfileV97D6U04M0367_profile (And.intro z180K30ProfileV97D6U04M0368_profile (And.intro z180K30ProfileV97D6U04M0369_profile (And.intro z180K30ProfileV97D6U04M0370_profile (And.intro z180K30ProfileV97D6U04M0371_profile (And.intro z180K30ProfileV97D6U04M0372_profile (And.intro z180K30ProfileV97D6U04M0373_profile (And.intro z180K30ProfileV97D6U04M0374_profile (And.intro z180K30ProfileV97D6U04M0375_profile (And.intro z180K30ProfileV97D6U04M0376_profile (And.intro z180K30ProfileV97D6U04M0377_profile (And.intro z180K30ProfileV97D6U04M0378_profile (z180K30ProfileV97D6U04M0379_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
