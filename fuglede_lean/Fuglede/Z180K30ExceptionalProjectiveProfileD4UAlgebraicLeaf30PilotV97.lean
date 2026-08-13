import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 30, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf30IndicesPilotV97 : List Nat := [68, 122, 67, 121, 66]

def z180K30ProjectiveD4ULeaf30TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 8] [17, 18, 26, 27, 35] 4

def z180K30ProjectiveD4ULeaf30KeysPilotV97 : List Nat := [3397, 18265, 7313, 7276, 7268]

theorem z180_k30_projective_d4_u_leaf_30_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf30IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf30TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_30_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf30TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf30KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_30_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf30KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
