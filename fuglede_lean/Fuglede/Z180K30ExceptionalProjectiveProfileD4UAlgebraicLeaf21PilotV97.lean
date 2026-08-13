import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 21, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf21IndicesPilotV97 : List Nat := [167, 148, 166, 147, 165]

def z180K30ProjectiveD4ULeaf21TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [15, 18, 24, 27, 33] 4

def z180K30ProjectiveD4ULeaf21KeysPilotV97 : List Nat := [40230, 19313, 11099, 10988, 10982]

theorem z180_k30_projective_d4_u_leaf_21_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf21IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf21TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_21_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf21TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf21KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_21_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf21KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
