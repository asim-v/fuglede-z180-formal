import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 08, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf08IndicesPilotV97 : List Nat := [137]

def z180K30ProjectiveD4ULeaf08TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [12, 18, 21, 27, 30] 5

def z180K30ProjectiveD4ULeaf08KeysPilotV97 : List Nat := [23797]

theorem z180_k30_projective_d4_u_leaf_08_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf08IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf08TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_08_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf08TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf08KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_08_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf08KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
