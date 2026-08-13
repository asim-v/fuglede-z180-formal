import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 11, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf11IndicesPilotV97 : List Nat := [131, 153, 130, 152, 129, 151, 128, 127, 150, 126]

def z180K30ProjectiveD4ULeaf11TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 3, 9] [12, 18, 21, 27, 30] 3

def z180K30ProjectiveD4ULeaf11KeysPilotV97 : List Nat := [63536, 59429, 59207, 59204, 51215, 50993, 50990, 50882, 50879, 50873]

theorem z180_k30_projective_d4_u_leaf_11_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf11IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf11TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_11_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf11TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf11KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_11_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf11KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
