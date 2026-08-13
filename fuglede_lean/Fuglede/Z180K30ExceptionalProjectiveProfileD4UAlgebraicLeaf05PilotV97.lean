import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 05, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf05IndicesPilotV97 : List Nat := [89, 22, 88, 21, 87]

def z180K30ProjectiveD4ULeaf05TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [11, 18, 20, 27, 29] 4

def z180K30ProjectiveD4ULeaf05KeysPilotV97 : List Nat := [34750, 7784, 5046, 4787, 4785]

theorem z180_k30_projective_d4_u_leaf_05_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf05IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf05TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_05_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf05TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf05KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_05_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf05KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
