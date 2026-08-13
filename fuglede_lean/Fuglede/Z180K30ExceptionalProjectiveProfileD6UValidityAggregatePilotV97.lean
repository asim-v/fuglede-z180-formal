import Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D6
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityGroupU09PilotV97

/-! Exact bounded D6 U-profile-validity theorem over the canonical DataD6 list.

Integration precondition: DataV97D6 retains the profile-list definition but
delegates this theorem to the present module, so it must not define the same
theorem when this aggregate is compiled.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem z180_k30_projective_u_profiles_valid_v97_d6 :
    projectiveUProfilesValidB_v97 6 z180K30ProjectiveUProfilesV97D6 = true := by
  have houter :
      List.Forall
        (fun profileClass =>
          profileClass.members.all
            (fun U => projectiveUProfileV97 6 U == profileClass.profile) = true)
        z180K30ProjectiveUProfilesV97D6 := by
    unfold z180K30ProjectiveUProfilesV97D6
    exact And.intro z180_k30_projective_d6_u_validity_class_u00_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u01_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u02_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u03_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u04_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u05_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u06_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u07_valid_pilot_v97 (And.intro z180_k30_projective_d6_u_validity_class_u08_valid_pilot_v97 (z180_k30_projective_d6_u_validity_class_u09_valid_pilot_v97)))))))))
  unfold projectiveUProfilesValidB_v97
  apply List.all_eq_true.mpr
  intro profileClass hprofileClass
  exact (List.forall_iff_forall_mem.mp houter) profileClass hprofileClass

end Fuglede.Z180K30ExceptionalRawV2
