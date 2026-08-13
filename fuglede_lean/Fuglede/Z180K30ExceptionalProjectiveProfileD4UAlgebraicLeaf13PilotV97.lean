import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 13, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf13IndicesPilotV97 : List Nat := [98, 34, 97, 33, 96]

def z180K30ProjectiveD4ULeaf13TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [13, 18, 22, 27, 31] 4

def z180K30ProjectiveD4ULeaf13KeysPilotV97 : List Nat := [37490, 46309, 40833, 40648, 40644]

theorem z180_k30_projective_d4_u_leaf_13_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf13IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf13TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_13_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf13TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf13KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_13_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf13KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
