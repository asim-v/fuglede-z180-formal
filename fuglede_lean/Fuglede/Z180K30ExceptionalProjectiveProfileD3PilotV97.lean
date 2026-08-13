import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97

/-! Minimal source-only pilot: one U/V profile, one negative cell, one exact positive lookup. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveProfilePilotV97U : RawSet := [0, 2, 12, 14, 24, 26]
def z180K30ProjectiveProfilePilotV97V : RawSet := [0, 3, 6, 18, 21, 24]

theorem z180_k30_projective_profile_pilot_v97_u :
    projectiveUProfileV97 3 z180K30ProjectiveProfilePilotV97U =
      [36, 0, 0, 27, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0, 27, 0, 0, 36, 0, 0, 27, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0, 27, 0, 0] := by
  decide

theorem z180_k30_projective_profile_pilot_v97_v :
    projectiveVProfileV97 3 z180K30ProjectiveProfilePilotV97V =
      [0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 6, 6, 12, 12, 15, 15, 15, 15, 18, 18, 18, 18, 18, 18, 21, 21, 21, 21, 24, 24, 30, 30, 33, 33, 33, 33] := by
  apply projectiveVProfileV97_eq_of_perm_sorted
  · decide
  · decide

theorem z180_k30_projective_profile_pilot_v97_v_divisible :
    projectiveSideDivisibleB_v97 3 z180K30ProjectiveProfilePilotV97V = true := by
  decide

theorem z180_k30_projective_profile_pilot_v97_negative :
    projectiveProfileDotV97
      [36, 0, 0, 18, 0, 0, 27, 0, 0, 18, 0, 0, 9, 0, 0, 18, 0, 0, 0, 0, 0, 18, 0, 0, 9, 0, 0, 18, 0, 0, 27, 0, 0, 18, 0, 0]
      [0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 6, 6, 6, 6, 9, 9, 9, 12, 12, 15, 21, 24, 24, 27, 27, 27, 30, 30, 30, 30, 33, 33, 33, 33, 33] =
        792 := by
  decide

def z180K30ProjectiveProfilePilotV97NegativeU : RawSet :=
  [0, 1, 12, 13, 24, 25]
def z180K30ProjectiveProfilePilotV97NegativeV : RawSet :=
  [0, 3, 6, 9, 12, 15]

def z180K30ProjectiveProfilePilotV97NegativeUClasses :
    List ProjectiveProfileClassV97 :=
  [⟨[36, 0, 0, 18, 0, 0, 27, 0, 0, 18, 0, 0, 9, 0, 0, 18, 0, 0, 0, 0, 0, 18, 0, 0, 9, 0, 0, 18, 0, 0, 27, 0, 0, 18, 0, 0],
    [z180K30ProjectiveProfilePilotV97NegativeU]⟩]

def z180K30ProjectiveProfilePilotV97NegativeVClasses :
    List ProjectiveVProfileClassV97 :=
  [⟨[0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 6, 6, 6, 6, 9, 9, 9, 12, 12, 15, 21, 24, 24, 27, 27, 27, 30, 30, 30, 30, 33, 33, 33, 33, 33],
    [z180K30ProjectiveProfilePilotV97NegativeV]⟩]

theorem z180_k30_projective_profile_pilot_v97_negative_cell :
    projectiveProfileCellCoveredB_v97 3
      z180K30ProjectiveProfilePilotV97NegativeUClasses
      z180K30ProjectiveProfilePilotV97NegativeVClasses [] 0 0 = true := by
  decide

def z180K30ProjectiveProfilePilotV97UClasses :
    List ProjectiveProfileClassV97 :=
  [⟨[36, 0, 0, 27, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0, 27, 0, 0, 36, 0, 0, 27, 0, 0, 9, 0, 0, 0, 0, 0, 9, 0, 0, 27, 0, 0], [z180K30ProjectiveProfilePilotV97U]⟩]

def z180K30ProjectiveProfilePilotV97VClasses :
    List ProjectiveVProfileClassV97 :=
  [⟨[0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 6, 6, 12, 12, 15, 15, 15, 15, 18, 18, 18, 18, 18, 18, 21, 21, 21, 21, 24, 24, 30, 30, 33, 33, 33, 33], [z180K30ProjectiveProfilePilotV97V]⟩]

def z180K30ProjectiveProfilePilotV97Lookup :
    ProjectiveProfileWitnessLookupV97 :=
  ⟨0, 0, 0, 0, 0, 18⟩

theorem z180_k30_projective_profile_pilot_v97_positive_lookup :
    projectiveProfileLookupB_v97 3
      z180K30ProjectiveProfilePilotV97UClasses
      z180K30ProjectiveProfilePilotV97VClasses
      z180K30ProjectiveProfilePilotV97Lookup = true := by
  decide

theorem z180_k30_projective_profile_pilot_v97_positive_cell :
    projectiveProfileCellCoveredB_v97 3
      z180K30ProjectiveProfilePilotV97UClasses
      z180K30ProjectiveProfilePilotV97VClasses
      [z180K30ProjectiveProfilePilotV97Lookup] 0 0 = true := by
  decide

#print axioms z180_k30_projective_profile_pilot_v97_u
#print axioms z180_k30_projective_profile_pilot_v97_v
#print axioms z180_k30_projective_profile_pilot_v97_negative
#print axioms z180_k30_projective_profile_pilot_v97_negative_cell
#print axioms z180_k30_projective_profile_pilot_v97_positive_lookup
#print axioms z180_k30_projective_profile_pilot_v97_positive_cell

end Fuglede.Z180K30ExceptionalRawV2
