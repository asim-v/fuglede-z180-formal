import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 15, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf15IndicesPilotV97 : List Nat := [29, 93, 28, 92, 27, 91, 26, 25, 90, 24]

def z180K30ProjectiveD4ULeaf15TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 4, 9] [13, 18, 22, 27, 31] 3

def z180K30ProjectiveD4ULeaf15KeysPilotV97 : List Nat := [38958, 33482, 33297, 33293, 26637, 26452, 26448, 26304, 26300, 26295]

theorem z180_k30_projective_d4_u_leaf_15_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf15IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf15TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_15_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf15TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf15KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_15_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf15KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
