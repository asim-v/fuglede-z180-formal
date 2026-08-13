import Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D6

/-! Generated 213-cell audit row for divisor 6, U profile 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2



set_option maxRecDepth 100000 in
@[simp] theorem z180_k30_projective_profile_cell_v97_d6_u01_v00 :
    projectiveProfileCellCoveredB_v97 6
      z180K30ProjectiveUProfilesV97D6 z180K30ProjectiveVProfilesV97D6
      (z180K30ProjectiveProfileLookupForV97D6 1 0)
      1 0 = true := by
  decide

@[simp] theorem z180_k30_projective_profile_row_v97_d6_u01 :
    (List.range z180K30ProjectiveVProfilesV97D6.length).all fun vIndex =>
      projectiveProfileCellCoveredB_v97 6
        z180K30ProjectiveUProfilesV97D6 z180K30ProjectiveVProfilesV97D6
        (z180K30ProjectiveProfileLookupForV97D6 1 vIndex)
        1 vIndex = true := by
  simpa [z180K30ProjectiveVProfilesV97D6] using z180_k30_projective_profile_cell_v97_d6_u01_v00

end Fuglede.Z180K30ExceptionalRawV2
