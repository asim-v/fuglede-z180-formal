import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S097
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S098

/-! Bounded D6 U-validity leaf U07C05: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU07C05PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U07M0100, z180K30ProfileV97D6U07M0101, z180K30ProfileV97D6U07M0102, z180K30ProfileV97D6U07M0103, z180K30ProfileV97D6U07M0104, z180K30ProfileV97D6U07M0105, z180K30ProfileV97D6U07M0106, z180K30ProfileV97D6U07M0107, z180K30ProfileV97D6U07M0108, z180K30ProfileV97D6U07M0109, z180K30ProfileV97D6U07M0110, z180K30ProfileV97D6U07M0111, z180K30ProfileV97D6U07M0112, z180K30ProfileV97D6U07M0113, z180K30ProfileV97D6U07M0114, z180K30ProfileV97D6U07M0115, z180K30ProfileV97D6U07M0116, z180K30ProfileV97D6U07M0117, z180K30ProfileV97D6U07M0118, z180K30ProfileV97D6U07M0119]

theorem z180_k30_projective_d6_u_validity_members_u07c05_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU07PilotV97)
      z180K30ProjectiveD6UValidityMembersU07C05PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU07C05PilotV97 z180K30ProjectiveD6UValidityProfileU07PilotV97
  exact And.intro z180K30ProfileV97D6U07M0100_profile (And.intro z180K30ProfileV97D6U07M0101_profile (And.intro z180K30ProfileV97D6U07M0102_profile (And.intro z180K30ProfileV97D6U07M0103_profile (And.intro z180K30ProfileV97D6U07M0104_profile (And.intro z180K30ProfileV97D6U07M0105_profile (And.intro z180K30ProfileV97D6U07M0106_profile (And.intro z180K30ProfileV97D6U07M0107_profile (And.intro z180K30ProfileV97D6U07M0108_profile (And.intro z180K30ProfileV97D6U07M0109_profile (And.intro z180K30ProfileV97D6U07M0110_profile (And.intro z180K30ProfileV97D6U07M0111_profile (And.intro z180K30ProfileV97D6U07M0112_profile (And.intro z180K30ProfileV97D6U07M0113_profile (And.intro z180K30ProfileV97D6U07M0114_profile (And.intro z180K30ProfileV97D6U07M0115_profile (And.intro z180K30ProfileV97D6U07M0116_profile (And.intro z180K30ProfileV97D6U07M0117_profile (And.intro z180K30ProfileV97D6U07M0118_profile (z180K30ProfileV97D6U07M0119_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
