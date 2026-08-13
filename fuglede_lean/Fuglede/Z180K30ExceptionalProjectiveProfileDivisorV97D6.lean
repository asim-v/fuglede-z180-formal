import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U00
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U01
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U02
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U03
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U04
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U05
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U06
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U07
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U08
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D6U09
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UValidityAggregatePilotV97

/-! Generated certified profile audit for divisor 6. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
def z180K30CertifiedProjectiveProfileAuditV97D6 :
    CertifiedNormalizedProjectiveProfileAuditV97 6 where
  uProfiles := z180K30ProjectiveUProfilesV97D6
  vProfiles := z180K30ProjectiveVProfilesV97D6
  lookupFor := z180K30ProjectiveProfileLookupForV97D6
  uMembers_complete :=
    z180_k30_projective_u_profile_members_complete_v97_d6
  vMembers_complete :=
    z180_k30_projective_v_profile_members_complete_v97_d6
  uProfiles_valid := z180_k30_projective_u_profiles_valid_v97_d6
  vProfiles_valid := z180_k30_projective_v_profiles_valid_v97_d6
  vProfiles_divisible :=
    z180_k30_projective_v_profiles_divisible_v97_d6
  cells_covered := by
    unfold projectiveProfileAllCellsCoveredB_v97
    apply List.all_eq_true.mpr
    intro uIndex huIndex
    simp only [List.mem_range] at huIndex
    change uIndex < 10 at huIndex
    interval_cases uIndex <;> first
      | exact z180_k30_projective_profile_row_v97_d6_u00
      | exact z180_k30_projective_profile_row_v97_d6_u01
      | exact z180_k30_projective_profile_row_v97_d6_u02
      | exact z180_k30_projective_profile_row_v97_d6_u03
      | exact z180_k30_projective_profile_row_v97_d6_u04
      | exact z180_k30_projective_profile_row_v97_d6_u05
      | exact z180_k30_projective_profile_row_v97_d6_u06
      | exact z180_k30_projective_profile_row_v97_d6_u07
      | exact z180_k30_projective_profile_row_v97_d6_u08
      | exact z180_k30_projective_profile_row_v97_d6_u09

#print axioms z180K30CertifiedProjectiveProfileAuditV97D6

end Fuglede.Z180K30ExceptionalRawV2
