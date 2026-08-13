import Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D4

/-! Generated 213-cell audit row for divisor 4, U profile 2. -/

namespace Fuglede.Z180K30ExceptionalRawV2



@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v00 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 0)
      2 0 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v01 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 1)
      2 1 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v02 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 2)
      2 2 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v03 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 3)
      2 3 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v04 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 4)
      2 4 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v05 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 5)
      2 5 = true := by
  decide
@[simp] theorem z180_k30_projective_profile_cell_v97_d4_u02_v06 :
    projectiveProfileCellCoveredB_v97 4
      z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
      (z180K30ProjectiveProfileLookupForV97D4 2 6)
      2 6 = true := by
  decide

@[simp] theorem z180_k30_projective_profile_row_v97_d4_u02 :
    (List.range z180K30ProjectiveVProfilesV97D4.length).all fun vIndex =>
      projectiveProfileCellCoveredB_v97 4
        z180K30ProjectiveUProfilesV97D4 z180K30ProjectiveVProfilesV97D4
        (z180K30ProjectiveProfileLookupForV97D4 2 vIndex)
        2 vIndex = true := by
  apply List.all_eq_true.mpr
  intro vIndex hvIndex
  simp only [List.mem_range] at hvIndex
  change vIndex < 7 at hvIndex
  interval_cases vIndex <;> simp

end Fuglede.Z180K30ExceptionalRawV2
