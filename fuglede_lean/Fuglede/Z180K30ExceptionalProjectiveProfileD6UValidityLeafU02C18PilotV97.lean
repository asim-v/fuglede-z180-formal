import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S038
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S039

/-! Bounded D6 U-validity leaf U02C18: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C18PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0360, z180K30ProfileV97D6U02M0361, z180K30ProfileV97D6U02M0362, z180K30ProfileV97D6U02M0363, z180K30ProfileV97D6U02M0364, z180K30ProfileV97D6U02M0365, z180K30ProfileV97D6U02M0366, z180K30ProfileV97D6U02M0367, z180K30ProfileV97D6U02M0368, z180K30ProfileV97D6U02M0369, z180K30ProfileV97D6U02M0370, z180K30ProfileV97D6U02M0371, z180K30ProfileV97D6U02M0372, z180K30ProfileV97D6U02M0373, z180K30ProfileV97D6U02M0374, z180K30ProfileV97D6U02M0375, z180K30ProfileV97D6U02M0376, z180K30ProfileV97D6U02M0377, z180K30ProfileV97D6U02M0378, z180K30ProfileV97D6U02M0379]

theorem z180_k30_projective_d6_u_validity_members_u02c18_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C18PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C18PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0360_profile (And.intro z180K30ProfileV97D6U02M0361_profile (And.intro z180K30ProfileV97D6U02M0362_profile (And.intro z180K30ProfileV97D6U02M0363_profile (And.intro z180K30ProfileV97D6U02M0364_profile (And.intro z180K30ProfileV97D6U02M0365_profile (And.intro z180K30ProfileV97D6U02M0366_profile (And.intro z180K30ProfileV97D6U02M0367_profile (And.intro z180K30ProfileV97D6U02M0368_profile (And.intro z180K30ProfileV97D6U02M0369_profile (And.intro z180K30ProfileV97D6U02M0370_profile (And.intro z180K30ProfileV97D6U02M0371_profile (And.intro z180K30ProfileV97D6U02M0372_profile (And.intro z180K30ProfileV97D6U02M0373_profile (And.intro z180K30ProfileV97D6U02M0374_profile (And.intro z180K30ProfileV97D6U02M0375_profile (And.intro z180K30ProfileV97D6U02M0376_profile (And.intro z180K30ProfileV97D6U02M0377_profile (And.intro z180K30ProfileV97D6U02M0378_profile (z180K30ProfileV97D6U02M0379_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
