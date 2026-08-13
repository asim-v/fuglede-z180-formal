import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S040
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S041

/-! Bounded D6 U-validity leaf U02C20: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C20PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0400, z180K30ProfileV97D6U02M0401, z180K30ProfileV97D6U02M0402, z180K30ProfileV97D6U02M0403, z180K30ProfileV97D6U02M0404, z180K30ProfileV97D6U02M0405, z180K30ProfileV97D6U02M0406, z180K30ProfileV97D6U02M0407, z180K30ProfileV97D6U02M0408, z180K30ProfileV97D6U02M0409, z180K30ProfileV97D6U02M0410, z180K30ProfileV97D6U02M0411, z180K30ProfileV97D6U02M0412, z180K30ProfileV97D6U02M0413, z180K30ProfileV97D6U02M0414, z180K30ProfileV97D6U02M0415, z180K30ProfileV97D6U02M0416, z180K30ProfileV97D6U02M0417, z180K30ProfileV97D6U02M0418, z180K30ProfileV97D6U02M0419]

theorem z180_k30_projective_d6_u_validity_members_u02c20_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C20PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C20PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0400_profile (And.intro z180K30ProfileV97D6U02M0401_profile (And.intro z180K30ProfileV97D6U02M0402_profile (And.intro z180K30ProfileV97D6U02M0403_profile (And.intro z180K30ProfileV97D6U02M0404_profile (And.intro z180K30ProfileV97D6U02M0405_profile (And.intro z180K30ProfileV97D6U02M0406_profile (And.intro z180K30ProfileV97D6U02M0407_profile (And.intro z180K30ProfileV97D6U02M0408_profile (And.intro z180K30ProfileV97D6U02M0409_profile (And.intro z180K30ProfileV97D6U02M0410_profile (And.intro z180K30ProfileV97D6U02M0411_profile (And.intro z180K30ProfileV97D6U02M0412_profile (And.intro z180K30ProfileV97D6U02M0413_profile (And.intro z180K30ProfileV97D6U02M0414_profile (And.intro z180K30ProfileV97D6U02M0415_profile (And.intro z180K30ProfileV97D6U02M0416_profile (And.intro z180K30ProfileV97D6U02M0417_profile (And.intro z180K30ProfileV97D6U02M0418_profile (z180K30ProfileV97D6U02M0419_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
