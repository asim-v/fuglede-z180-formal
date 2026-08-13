import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 10, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf10IndicesPilotV97 : List Nat := [134, 155, 133, 154, 132]

def z180K30ProjectiveD4ULeaf10TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 3] [12, 18, 21, 27, 30] 4

def z180K30ProjectiveD4ULeaf10KeysPilotV97 : List Nat := [60766, 18932, 14825, 14603, 14600]

theorem z180_k30_projective_d4_u_leaf_10_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf10IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf10TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_10_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf10TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf10KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_10_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf10KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
