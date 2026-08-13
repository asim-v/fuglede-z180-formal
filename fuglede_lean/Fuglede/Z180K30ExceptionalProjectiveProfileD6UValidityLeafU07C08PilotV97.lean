import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S100
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S101

/-! Bounded D6 U-validity leaf U07C08: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07C08PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U07M0160, z180K30ProfileV97D6U07M0161, z180K30ProfileV97D6U07M0162, z180K30ProfileV97D6U07M0163, z180K30ProfileV97D6U07M0164, z180K30ProfileV97D6U07M0165, z180K30ProfileV97D6U07M0166, z180K30ProfileV97D6U07M0167, z180K30ProfileV97D6U07M0168, z180K30ProfileV97D6U07M0169, z180K30ProfileV97D6U07M0170, z180K30ProfileV97D6U07M0171, z180K30ProfileV97D6U07M0172, z180K30ProfileV97D6U07M0173, z180K30ProfileV97D6U07M0174, z180K30ProfileV97D6U07M0175, z180K30ProfileV97D6U07M0176, z180K30ProfileV97D6U07M0177, z180K30ProfileV97D6U07M0178, z180K30ProfileV97D6U07M0179]

theorem z180_k30_projective_d6_u_validity_members_u07c08_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07C08PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07C08PilotV97 z180K30ProjectiveD6UValidityProfileU07PilotV97
  exact And.intro z180K30ProfileV97D6U07M0160_profile (And.intro z180K30ProfileV97D6U07M0161_profile (And.intro z180K30ProfileV97D6U07M0162_profile (And.intro z180K30ProfileV97D6U07M0163_profile (And.intro z180K30ProfileV97D6U07M0164_profile (And.intro z180K30ProfileV97D6U07M0165_profile (And.intro z180K30ProfileV97D6U07M0166_profile (And.intro z180K30ProfileV97D6U07M0167_profile (And.intro z180K30ProfileV97D6U07M0168_profile (And.intro z180K30ProfileV97D6U07M0169_profile (And.intro z180K30ProfileV97D6U07M0170_profile (And.intro z180K30ProfileV97D6U07M0171_profile (And.intro z180K30ProfileV97D6U07M0172_profile (And.intro z180K30ProfileV97D6U07M0173_profile (And.intro z180K30ProfileV97D6U07M0174_profile (And.intro z180K30ProfileV97D6U07M0175_profile (And.intro z180K30ProfileV97D6U07M0176_profile (And.intro z180K30ProfileV97D6U07M0177_profile (And.intro z180K30ProfileV97D6U07M0178_profile (z180K30ProfileV97D6U07M0179_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
