import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D4U00
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D4U01
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D4U02
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D4U03

/-! Generated certified profile audit for divisor 4. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30CertifiedProjectiveProfileAuditV97D4 :
    CertifiedNormalizedProjectiveProfileAuditV97 4 where
  uProfiles := z180K30ProjectiveUProfilesV97D4
  vProfiles := z180K30ProjectiveVProfilesV97D4
  lookupFor := z180K30ProjectiveProfileLookupForV97D4
  uMembers_complete :=
    z180_k30_projective_u_profile_members_complete_v97_d4
  vMembers_complete :=
    z180_k30_projective_v_profile_members_complete_v97_d4
  uProfiles_valid := z180_k30_projective_u_profiles_valid_v97_d4
  vProfiles_valid := z180_k30_projective_v_profiles_valid_v97_d4
  vProfiles_divisible :=
    z180_k30_projective_v_profiles_divisible_v97_d4
  cells_covered := by
    unfold projectiveProfileAllCellsCoveredB_v97
    apply List.all_eq_true.mpr
    intro uIndex huIndex
    simp only [List.mem_range] at huIndex
    change uIndex < 4 at huIndex
    interval_cases uIndex <;> first
      | exact z180_k30_projective_profile_row_v97_d4_u00
      | exact z180_k30_projective_profile_row_v97_d4_u01
      | exact z180_k30_projective_profile_row_v97_d4_u02
      | exact z180_k30_projective_profile_row_v97_d4_u03

#print axioms z180K30CertifiedProjectiveProfileAuditV97D4

end Fuglede.Z180K30ExceptionalRawV2
