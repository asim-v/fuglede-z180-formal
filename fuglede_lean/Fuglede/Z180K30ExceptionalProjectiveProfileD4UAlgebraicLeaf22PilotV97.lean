import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 22, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf22IndicesPilotV97 : List Nat := [146, 164, 145, 163, 144]

def z180K30ProjectiveD4ULeaf22TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 6] [15, 18, 24, 27, 33] 4

def z180K30ProjectiveD4ULeaf22KeysPilotV97 : List Nat := [52553, 31636, 23422, 23311, 23305]

theorem z180_k30_projective_d4_u_leaf_22_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf22IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf22TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_22_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf22TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf22KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_22_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf22KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
