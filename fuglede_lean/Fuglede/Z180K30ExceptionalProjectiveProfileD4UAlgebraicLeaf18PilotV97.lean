import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 18, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf18IndicesPilotV97 : List Nat := [44, 104, 43, 103, 42]

def z180K30ProjectiveD4ULeaf18TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 5] [14, 18, 23, 27, 32] 4

def z180K30ProjectiveD4ULeaf18KeysPilotV97 : List Nat := [11610, 5561, 64237, 64089, 64084]

theorem z180_k30_projective_d4_u_leaf_18_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf18IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf18TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_18_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf18TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf18KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_18_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf18KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
