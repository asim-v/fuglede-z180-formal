import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 04, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf04IndicesPilotV97 : List Nat := [23]

def z180K30ProjectiveD4ULeaf04TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [11, 18, 20, 27, 29] 5

def z180K30ProjectiveD4ULeaf04KeysPilotV97 : List Nat := [48375]

theorem z180_k30_projective_d4_u_leaf_04_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf04IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf04TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_04_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf04TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf04KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_04_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf04KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
