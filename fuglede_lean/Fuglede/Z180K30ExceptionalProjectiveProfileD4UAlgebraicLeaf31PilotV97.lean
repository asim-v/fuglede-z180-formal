import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 31, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf31IndicesPilotV97 : List Nat := [65, 120, 64, 119, 63, 118, 62, 61, 117, 60]

def z180K30ProjectiveD4ULeaf31TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 8, 9] [17, 18, 26, 27, 35] 3

def z180K30ProjectiveD4ULeaf31KeysPilotV97 : List Nat := [6167, 60736, 60699, 60691, 59367, 59330, 59322, 59034, 59026, 59025]

theorem z180_k30_projective_d4_u_leaf_31_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf31IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf31TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_31_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf31TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf31KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_31_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf31KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
