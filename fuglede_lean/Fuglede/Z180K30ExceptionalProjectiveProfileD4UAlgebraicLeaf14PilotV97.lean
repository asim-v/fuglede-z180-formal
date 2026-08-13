import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 14, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf14IndicesPilotV97 : List Nat := [32, 95, 31, 94, 30]

def z180K30ProjectiveD4ULeaf14TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 4] [13, 18, 22, 27, 31] 4

def z180K30ProjectiveD4ULeaf14KeysPilotV97 : List Nat := [36188, 45007, 39531, 39346, 39342]

theorem z180_k30_projective_d4_u_leaf_14_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf14IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf14TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_14_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf14TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf14KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_14_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf14KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
