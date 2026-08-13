import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 25, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf25IndicesPilotV97 : List Nat := [116, 58, 115, 57, 114]

def z180K30ProjectiveD4ULeaf25TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [16, 18, 25, 27, 34] 4

def z180K30ProjectiveD4ULeaf25KeysPilotV97 : List Nat := [41600, 5815, 61753, 61679, 61672]

theorem z180_k30_projective_d4_u_leaf_25_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf25IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf25TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_25_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf25TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf25KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_25_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf25KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
