import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 27, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf27IndicesPilotV97 : List Nat := [53, 111, 52, 110, 51, 109, 50, 49, 108, 48]

def z180K30ProjectiveD4ULeaf27TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 7, 9] [16, 18, 25, 27, 34] 3

def z180K30ProjectiveD4ULeaf27KeysPilotV97 : List Nat := [30745, 21162, 21088, 21081, 18424, 18350, 18343, 18091, 18084, 18082]

theorem z180_k30_projective_d4_u_leaf_27_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf27IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf27TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_27_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf27TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf27KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_27_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf27KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
