import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S022
import Fuglede.Z180K30ExceptionalProjectiveProfileMembersV97D6S023

/-! Bounded D6 U-validity leaf U02C02: 20 certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UValidityMembersU02C02PilotV97 : List RawSet :=
  [z180K30ProfileV97D6U02M0040, z180K30ProfileV97D6U02M0041, z180K30ProfileV97D6U02M0042, z180K30ProfileV97D6U02M0043, z180K30ProfileV97D6U02M0044, z180K30ProfileV97D6U02M0045, z180K30ProfileV97D6U02M0046, z180K30ProfileV97D6U02M0047, z180K30ProfileV97D6U02M0048, z180K30ProfileV97D6U02M0049, z180K30ProfileV97D6U02M0050, z180K30ProfileV97D6U02M0051, z180K30ProfileV97D6U02M0052, z180K30ProfileV97D6U02M0053, z180K30ProfileV97D6U02M0054, z180K30ProfileV97D6U02M0055, z180K30ProfileV97D6U02M0056, z180K30ProfileV97D6U02M0057, z180K30ProfileV97D6U02M0058, z180K30ProfileV97D6U02M0059]

theorem z180_k30_projective_d6_u_validity_members_u02c02_forall_pilot_v97 :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = z180K30ProjectiveD6UValidityProfileU02PilotV97)
      z180K30ProjectiveD6UValidityMembersU02C02PilotV97 := by
  unfold z180K30ProjectiveD6UValidityMembersU02C02PilotV97 z180K30ProjectiveD6UValidityProfileU02PilotV97
  exact And.intro z180K30ProfileV97D6U02M0040_profile (And.intro z180K30ProfileV97D6U02M0041_profile (And.intro z180K30ProfileV97D6U02M0042_profile (And.intro z180K30ProfileV97D6U02M0043_profile (And.intro z180K30ProfileV97D6U02M0044_profile (And.intro z180K30ProfileV97D6U02M0045_profile (And.intro z180K30ProfileV97D6U02M0046_profile (And.intro z180K30ProfileV97D6U02M0047_profile (And.intro z180K30ProfileV97D6U02M0048_profile (And.intro z180K30ProfileV97D6U02M0049_profile (And.intro z180K30ProfileV97D6U02M0050_profile (And.intro z180K30ProfileV97D6U02M0051_profile (And.intro z180K30ProfileV97D6U02M0052_profile (And.intro z180K30ProfileV97D6U02M0053_profile (And.intro z180K30ProfileV97D6U02M0054_profile (And.intro z180K30ProfileV97D6U02M0055_profile (And.intro z180K30ProfileV97D6U02M0056_profile (And.intro z180K30ProfileV97D6U02M0057_profile (And.intro z180K30ProfileV97D6U02M0058_profile (z180K30ProfileV97D6U02M0059_profile)))))))))))))))))))

end Fuglede.Z180K30ExceptionalRawV2
