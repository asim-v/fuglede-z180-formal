import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D3U00
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D3U01
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D3U02
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D3U03
import Fuglede.Z180K30ExceptionalProjectiveProfileCellsV97D3U04

/-! Generated certified profile audit for divisor 3. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30CertifiedProjectiveProfileAuditV97D3 :
    CertifiedNormalizedProjectiveProfileAuditV97 3 where
  uProfiles := z180K30ProjectiveUProfilesV97D3
  vProfiles := z180K30ProjectiveVProfilesV97D3
  lookupFor := z180K30ProjectiveProfileLookupForV97D3
  uMembers_complete :=
    z180_k30_projective_u_profile_members_complete_v97_d3
  vMembers_complete :=
    z180_k30_projective_v_profile_members_complete_v97_d3
  uProfiles_valid := z180_k30_projective_u_profiles_valid_v97_d3
  vProfiles_valid := z180_k30_projective_v_profiles_valid_v97_d3
  vProfiles_divisible :=
    z180_k30_projective_v_profiles_divisible_v97_d3
  cells_covered := by
    unfold projectiveProfileAllCellsCoveredB_v97
    apply List.all_eq_true.mpr
    intro uIndex huIndex
    simp only [List.mem_range] at huIndex
    change uIndex < 5 at huIndex
    interval_cases uIndex <;> first
      | exact z180_k30_projective_profile_row_v97_d3_u00
      | exact z180_k30_projective_profile_row_v97_d3_u01
      | exact z180_k30_projective_profile_row_v97_d3_u02
      | exact z180_k30_projective_profile_row_v97_d3_u03
      | exact z180_k30_projective_profile_row_v97_d3_u04

#print axioms z180K30CertifiedProjectiveProfileAuditV97D3

end Fuglede.Z180K30ExceptionalRawV2
