import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S005
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S006

/-! Bounded D6 U-validity leaf U01C05: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU01C05PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U01M0100, z180K30ProfileV97D6U01M0101, z180K30ProfileV97D6U01M0102, z180K30ProfileV97D6U01M0103, z180K30ProfileV97D6U01M0104, z180K30ProfileV97D6U01M0105, z180K30ProfileV97D6U01M0106, z180K30ProfileV97D6U01M0107, z180K30ProfileV97D6U01M0108, z180K30ProfileV97D6U01M0109, z180K30ProfileV97D6U01M0110, z180K30ProfileV97D6U01M0111, z180K30ProfileV97D6U01M0112, z180K30ProfileV97D6U01M0113, z180K30ProfileV97D6U01M0114, z180K30ProfileV97D6U01M0115, z180K30ProfileV97D6U01M0116, z180K30ProfileV97D6U01M0117, z180K30ProfileV97D6U01M0118, z180K30ProfileV97D6U01M0119]

theorem z180_k30_projective_d6_u_validity_members_u01c05_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU01PilotV97)
      z180K30ProjectiveD6UValidityMembersU01C05PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU01C05PilotV97 z180K30ProjectiveD6UValidityProfileU01PilotV97
  exact And.intro z180K30ProfileV97D6U01M0100_profile (And.intro z180K30ProfileV97D6U01M0101_profile (And.intro z180K30ProfileV97D6U01M0102_profile (And.intro z180K30ProfileV97D6U01M0103_profile (And.intro z180K30ProfileV97D6U01M0104_profile (And.intro z180K30ProfileV97D6U01M0105_profile (And.intro z180K30ProfileV97D6U01M0106_profile (And.intro z180K30ProfileV97D6U01M0107_profile (And.intro z180K30ProfileV97D6U01M0108_profile (And.intro z180K30ProfileV97D6U01M0109_profile (And.intro z180K30ProfileV97D6U01M0110_profile (And.intro z180K30ProfileV97D6U01M0111_profile (And.intro z180K30ProfileV97D6U01M0112_profile (And.intro z180K30ProfileV97D6U01M0113_profile (And.intro z180K30ProfileV97D6U01M0114_profile (And.intro z180K30ProfileV97D6U01M0115_profile (And.intro z180K30ProfileV97D6U01M0116_profile (And.intro z180K30ProfileV97D6U01M0117_profile (And.intro z180K30ProfileV97D6U01M0118_profile (z180K30ProfileV97D6U01M0119_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
