import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 16, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf16IndicesPilotV97 : List Nat := [47]

def z180K30ProjectiveD4ULeaf16TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [14, 18, 23, 27, 32] 5

def z180K30ProjectiveD4ULeaf16KeysPilotV97 : List Nat := [40162]

theorem z180_k30_projective_d4_u_leaf_16_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf16IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf16TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_16_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf16TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf16KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_16_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf16KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
