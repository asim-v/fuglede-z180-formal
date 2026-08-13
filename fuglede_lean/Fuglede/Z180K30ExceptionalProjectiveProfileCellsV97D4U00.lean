import Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D4

/-! Generated 213-cell audit row for divisor 4, U profile 0. -/

namespace Fuglede.Z180K30ExceptionalRawV2



@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v00 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 0)
      0 0 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v01 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 1)
      0 1 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v02 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 2)
      0 2 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v03 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 3)
      0 3 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v04 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 4)
      0 4 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v05 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 5)
      0 5 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u00_v06 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 0 6)
      0 6 = true := by
  decide

@[simp] theorem z180_k30_projective_profile_row_v97_d4_u00 :
    (List.range z180K30ProjectiveVProfilesV97D4.length).all fun vIndex =>
      projectiveProfileCellCoveredB_v97 4
        z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
        (z180K30ProjectiveProfileLookupForV97D4 0 vIndex)
        0 vIndex = true := by
  apply List.all_eq_true.mpr
  intro vIndex hvIndex
  simp only [List.mem_range] at hvIndex
  change vIndex < 7 at hvIndex
  interval_cases vIndex <;> simp

end Fuglede.Z180K30ExceptionalRawV2
