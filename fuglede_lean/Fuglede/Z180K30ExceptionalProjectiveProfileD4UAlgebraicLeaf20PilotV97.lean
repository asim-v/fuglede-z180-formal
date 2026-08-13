import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 20, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf20IndicesPilotV97 : List Nat := [149]

def z180K30ProjectiveD4ULeaf20TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [15, 18, 24, 27, 33] 5

def z180K30ProjectiveD4ULeaf20KeysPilotV97 : List Nat := [15584]

theorem z180_k30_projective_d4_u_leaf_20_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf20IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf20TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_20_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf20TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf20KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_20_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf20KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
