import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 26, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf26IndicesPilotV97 : List Nat := [56, 113, 55, 112, 54]

def z180K30ProjectiveD4ULeaf26TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 7] [16, 18, 25, 27, 34] 4

def z180K30ProjectiveD4ULeaf26KeysPilotV97 : List Nat := [27975, 57711, 48128, 48054, 48047]

theorem z180_k30_projective_d4_u_leaf_26_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf26IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf26TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_26_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf26TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf26KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_26_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf26KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
