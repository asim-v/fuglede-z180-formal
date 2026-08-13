import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 29, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf29IndicesPilotV97 : List Nat := [125, 70, 124, 69, 123]

def z180K30ProjectiveD4ULeaf29TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [17, 18, 26, 27, 35] 4

def z180K30ProjectiveD4ULeaf29KeysPilotV97 : List Nat := [42970, 57838, 46886, 46849, 46841]

theorem z180_k30_projective_d4_u_leaf_29_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf29IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf29TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_29_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf29TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf29KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_29_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf29KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
