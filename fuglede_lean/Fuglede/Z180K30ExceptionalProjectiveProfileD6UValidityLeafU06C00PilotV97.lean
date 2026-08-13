import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S088
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S089

/-! Bounded D6 U-validity leaf U06C00: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU06C00PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U06M0000, z180K30ProfileV97D6U06M0001, z180K30ProfileV97D6U06M0002, z180K30ProfileV97D6U06M0003, z180K30ProfileV97D6U06M0004, z180K30ProfileV97D6U06M0005, z180K30ProfileV97D6U06M0006, z180K30ProfileV97D6U06M0007, z180K30ProfileV97D6U06M0008, z180K30ProfileV97D6U06M0009, z180K30ProfileV97D6U06M0010, z180K30ProfileV97D6U06M0011, z180K30ProfileV97D6U06M0012, z180K30ProfileV97D6U06M0013, z180K30ProfileV97D6U06M0014, z180K30ProfileV97D6U06M0015, z180K30ProfileV97D6U06M0016, z180K30ProfileV97D6U06M0017, z180K30ProfileV97D6U06M0018, z180K30ProfileV97D6U06M0019]

theorem z180_k30_projective_d6_u_validity_members_u06c00_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU06PilotV97)
      z180K30ProjectiveD6UValidityMembersU06C00PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU06C00PilotV97 z180K30ProjectiveD6UValidityProfileU06PilotV97
  exact And.intro z180K30ProfileV97D6U06M0000_profile (And.intro z180K30ProfileV97D6U06M0001_profile (And.intro z180K30ProfileV97D6U06M0002_profile (And.intro z180K30ProfileV97D6U06M0003_profile (And.intro z180K30ProfileV97D6U06M0004_profile (And.intro z180K30ProfileV97D6U06M0005_profile (And.intro z180K30ProfileV97D6U06M0006_profile (And.intro z180K30ProfileV97D6U06M0007_profile (And.intro z180K30ProfileV97D6U06M0008_profile (And.intro z180K30ProfileV97D6U06M0009_profile (And.intro z180K30ProfileV97D6U06M0010_profile (And.intro z180K30ProfileV97D6U06M0011_profile (And.intro z180K30ProfileV97D6U06M0012_profile (And.intro z180K30ProfileV97D6U06M0013_profile (And.intro z180K30ProfileV97D6U06M0014_profile (And.intro z180K30ProfileV97D6U06M0015_profile (And.intro z180K30ProfileV97D6U06M0016_profile (And.intro z180K30ProfileV97D6U06M0017_profile (And.intro z180K30ProfileV97D6U06M0018_profile (z180K30ProfileV97D6U06M0019_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
