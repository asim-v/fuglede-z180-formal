import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S110
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S111

/-! Bounded D6 U-validity leaf U08C08: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU08C08PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U08M0160, z180K30ProfileV97D6U08M0161, z180K30ProfileV97D6U08M0162, z180K30ProfileV97D6U08M0163, z180K30ProfileV97D6U08M0164, z180K30ProfileV97D6U08M0165, z180K30ProfileV97D6U08M0166, z180K30ProfileV97D6U08M0167, z180K30ProfileV97D6U08M0168, z180K30ProfileV97D6U08M0169, z180K30ProfileV97D6U08M0170, z180K30ProfileV97D6U08M0171, z180K30ProfileV97D6U08M0172, z180K30ProfileV97D6U08M0173, z180K30ProfileV97D6U08M0174, z180K30ProfileV97D6U08M0175, z180K30ProfileV97D6U08M0176, z180K30ProfileV97D6U08M0177, z180K30ProfileV97D6U08M0178, z180K30ProfileV97D6U08M0179]

theorem z180_k30_projective_d6_u_validity_members_u08c08_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU08PilotV97)
      z180K30ProjectiveD6UValidityMembersU08C08PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU08C08PilotV97 z180K30ProjectiveD6UValidityProfileU08PilotV97
  exact And.intro z180K30ProfileV97D6U08M0160_profile (And.intro z180K30ProfileV97D6U08M0161_profile (And.intro z180K30ProfileV97D6U08M0162_profile (And.intro z180K30ProfileV97D6U08M0163_profile (And.intro z180K30ProfileV97D6U08M0164_profile (And.intro z180K30ProfileV97D6U08M0165_profile (And.intro z180K30ProfileV97D6U08M0166_profile (And.intro z180K30ProfileV97D6U08M0167_profile (And.intro z180K30ProfileV97D6U08M0168_profile (And.intro z180K30ProfileV97D6U08M0169_profile (And.intro z180K30ProfileV97D6U08M0170_profile (And.intro z180K30ProfileV97D6U08M0171_profile (And.intro z180K30ProfileV97D6U08M0172_profile (And.intro z180K30ProfileV97D6U08M0173_profile (And.intro z180K30ProfileV97D6U08M0174_profile (And.intro z180K30ProfileV97D6U08M0175_profile (And.intro z180K30ProfileV97D6U08M0176_profile (And.intro z180K30ProfileV97D6U08M0177_profile (And.intro z180K30ProfileV97D6U08M0178_profile (z180K30ProfileV97D6U08M0179_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
