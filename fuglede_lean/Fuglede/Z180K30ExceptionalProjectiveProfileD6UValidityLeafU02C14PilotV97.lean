import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S034
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S035

/-! Bounded D6 U-validity leaf U02C14: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C14PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0280, z180K30ProfileV97D6U02M0281, z180K30ProfileV97D6U02M0282, z180K30ProfileV97D6U02M0283, z180K30ProfileV97D6U02M0284, z180K30ProfileV97D6U02M0285, z180K30ProfileV97D6U02M0286, z180K30ProfileV97D6U02M0287, z180K30ProfileV97D6U02M0288, z180K30ProfileV97D6U02M0289, z180K30ProfileV97D6U02M0290, z180K30ProfileV97D6U02M0291, z180K30ProfileV97D6U02M0292, z180K30ProfileV97D6U02M0293, z180K30ProfileV97D6U02M0294, z180K30ProfileV97D6U02M0295, z180K30ProfileV97D6U02M0296, z180K30ProfileV97D6U02M0297, z180K30ProfileV97D6U02M0298, z180K30ProfileV97D6U02M0299]

theorem z180_k30_projective_d6_u_validity_members_u02c14_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C14PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C14PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0280_profile (And.intro z180K30ProfileV97D6U02M0281_profile (And.intro z180K30ProfileV97D6U02M0282_profile (And.intro z180K30ProfileV97D6U02M0283_profile (And.intro z180K30ProfileV97D6U02M0284_profile (And.intro z180K30ProfileV97D6U02M0285_profile (And.intro z180K30ProfileV97D6U02M0286_profile (And.intro z180K30ProfileV97D6U02M0287_profile (And.intro z180K30ProfileV97D6U02M0288_profile (And.intro z180K30ProfileV97D6U02M0289_profile (And.intro z180K30ProfileV97D6U02M0290_profile (And.intro z180K30ProfileV97D6U02M0291_profile (And.intro z180K30ProfileV97D6U02M0292_profile (And.intro z180K30ProfileV97D6U02M0293_profile (And.intro z180K30ProfileV97D6U02M0294_profile (And.intro z180K30ProfileV97D6U02M0295_profile (And.intro z180K30ProfileV97D6U02M0296_profile (And.intro z180K30ProfileV97D6U02M0297_profile (And.intro z180K30ProfileV97D6U02M0298_profile (z180K30ProfileV97D6U02M0299_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
