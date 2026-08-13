import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 09, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf09IndicesPilotV97 : List Nat := [158, 136, 157, 135, 156]

def z180K30ProjectiveD4ULeaf09TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [12, 18, 21, 27, 30] 4

def z180K30ProjectiveD4ULeaf09KeysPilotV97 : List Nat := [36120, 59807, 55700, 55478, 55475]

theorem z180_k30_projective_d4_u_leaf_09_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf09IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf09TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_09_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf09TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf09KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_09_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf09KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
