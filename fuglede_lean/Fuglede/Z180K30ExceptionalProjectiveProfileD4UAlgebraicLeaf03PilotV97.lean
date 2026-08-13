import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 03, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf03IndicesPilotV97 : List Nat := [5, 75, 4, 74, 3, 73, 2, 1, 72, 0]

def z180K30ProjectiveD4ULeaf03TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 1, 9] [10, 18, 19, 27, 28] 3

def z180K30ProjectiveD4ULeaf03KeysPilotV97 : List Nat := [47171, 45802, 45506, 45505, 34850, 34554, 34553, 34517, 34516, 34508]

theorem z180_k30_projective_d4_u_leaf_03_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf03IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf03TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_03_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf03TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf03KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_03_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf03KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
