import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S020
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S021

/-! Bounded D6 U-validity leaf U02C00: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C00PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0000, z180K30ProfileV97D6U02M0001, z180K30ProfileV97D6U02M0002, z180K30ProfileV97D6U02M0003, z180K30ProfileV97D6U02M0004, z180K30ProfileV97D6U02M0005, z180K30ProfileV97D6U02M0006, z180K30ProfileV97D6U02M0007, z180K30ProfileV97D6U02M0008, z180K30ProfileV97D6U02M0009, z180K30ProfileV97D6U02M0010, z180K30ProfileV97D6U02M0011, z180K30ProfileV97D6U02M0012, z180K30ProfileV97D6U02M0013, z180K30ProfileV97D6U02M0014, z180K30ProfileV97D6U02M0015, z180K30ProfileV97D6U02M0016, z180K30ProfileV97D6U02M0017, z180K30ProfileV97D6U02M0018, z180K30ProfileV97D6U02M0019]

theorem z180_k30_projective_d6_u_validity_members_u02c00_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C00PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C00PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0000_profile (And.intro z180K30ProfileV97D6U02M0001_profile (And.intro z180K30ProfileV97D6U02M0002_profile (And.intro z180K30ProfileV97D6U02M0003_profile (And.intro z180K30ProfileV97D6U02M0004_profile (And.intro z180K30ProfileV97D6U02M0005_profile (And.intro z180K30ProfileV97D6U02M0006_profile (And.intro z180K30ProfileV97D6U02M0007_profile (And.intro z180K30ProfileV97D6U02M0008_profile (And.intro z180K30ProfileV97D6U02M0009_profile (And.intro z180K30ProfileV97D6U02M0010_profile (And.intro z180K30ProfileV97D6U02M0011_profile (And.intro z180K30ProfileV97D6U02M0012_profile (And.intro z180K30ProfileV97D6U02M0013_profile (And.intro z180K30ProfileV97D6U02M0014_profile (And.intro z180K30ProfileV97D6U02M0015_profile (And.intro z180K30ProfileV97D6U02M0016_profile (And.intro z180K30ProfileV97D6U02M0017_profile (And.intro z180K30ProfileV97D6U02M0018_profile (z180K30ProfileV97D6U02M0019_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
