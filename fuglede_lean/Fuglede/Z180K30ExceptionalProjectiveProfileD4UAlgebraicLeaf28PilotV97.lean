import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 28, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf28IndicesPilotV97 : List Nat := [71]

def z180K30ProjectiveD4ULeaf28TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [17, 18, 26, 27, 35] 5

def z180K30ProjectiveD4ULeaf28KeysPilotV97 : List Nat := [31949]

theorem z180_k30_projective_d4_u_leaf_28_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf28IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf28TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_28_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf28TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf28KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_28_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf28KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
