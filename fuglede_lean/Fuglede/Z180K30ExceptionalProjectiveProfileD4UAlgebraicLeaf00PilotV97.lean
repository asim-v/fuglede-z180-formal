import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 00, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf00IndicesPilotV97 : List Nat := [11]

def z180K30ProjectiveD4ULeaf00TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [10, 18, 19, 27, 28] 5

def z180K30ProjectiveD4ULeaf00KeysPilotV97 : List Nat := [7432]

theorem z180_k30_projective_d4_u_leaf_00_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf00IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf00TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_00_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf00TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf00KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_00_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf00KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
