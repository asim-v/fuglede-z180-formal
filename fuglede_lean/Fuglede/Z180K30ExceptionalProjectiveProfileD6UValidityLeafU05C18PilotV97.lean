import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S084
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S085

/-! Bounded D6 U-validity leaf U05C18: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU05C18PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U05M0360, z180K30ProfileV97D6U05M0361, z180K30ProfileV97D6U05M0362, z180K30ProfileV97D6U05M0363, z180K30ProfileV97D6U05M0364, z180K30ProfileV97D6U05M0365, z180K30ProfileV97D6U05M0366, z180K30ProfileV97D6U05M0367, z180K30ProfileV97D6U05M0368, z180K30ProfileV97D6U05M0369, z180K30ProfileV97D6U05M0370, z180K30ProfileV97D6U05M0371, z180K30ProfileV97D6U05M0372, z180K30ProfileV97D6U05M0373, z180K30ProfileV97D6U05M0374, z180K30ProfileV97D6U05M0375, z180K30ProfileV97D6U05M0376, z180K30ProfileV97D6U05M0377, z180K30ProfileV97D6U05M0378, z180K30ProfileV97D6U05M0379]

theorem z180_k30_projective_d6_u_validity_members_u05c18_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU05PilotV97)
      z180K30ProjectiveD6UValidityMembersU05C18PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU05C18PilotV97 z180K30ProjectiveD6UValidityProfileU05PilotV97
  exact And.intro z180K30ProfileV97D6U05M0360_profile (And.intro z180K30ProfileV97D6U05M0361_profile (And.intro z180K30ProfileV97D6U05M0362_profile (And.intro z180K30ProfileV97D6U05M0363_profile (And.intro z180K30ProfileV97D6U05M0364_profile (And.intro z180K30ProfileV97D6U05M0365_profile (And.intro z180K30ProfileV97D6U05M0366_profile (And.intro z180K30ProfileV97D6U05M0367_profile (And.intro z180K30ProfileV97D6U05M0368_profile (And.intro z180K30ProfileV97D6U05M0369_profile (And.intro z180K30ProfileV97D6U05M0370_profile (And.intro z180K30ProfileV97D6U05M0371_profile (And.intro z180K30ProfileV97D6U05M0372_profile (And.intro z180K30ProfileV97D6U05M0373_profile (And.intro z180K30ProfileV97D6U05M0374_profile (And.intro z180K30ProfileV97D6U05M0375_profile (And.intro z180K30ProfileV97D6U05M0376_profile (And.intro z180K30ProfileV97D6U05M0377_profile (And.intro z180K30ProfileV97D6U05M0378_profile (z180K30ProfileV97D6U05M0379_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
