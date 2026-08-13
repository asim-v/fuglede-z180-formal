import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 01, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf01IndicesPilotV97 : List Nat := [80, 10, 79, 9, 78]

def z180K30ProjectiveD4ULeaf01TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [10, 18, 19, 27, 28] 4

def z180K30ProjectiveD4ULeaf01KeysPilotV97 : List Nat := [33380, 21282, 19913, 19617, 19616]

theorem z180_k30_projective_d4_u_leaf_01_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf01IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf01TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_01_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf01TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf01KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_01_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf01KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
