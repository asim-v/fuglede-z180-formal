import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 12, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf12IndicesPilotV97 : List Nat := [35]

def z180K30ProjectiveD4ULeaf12TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [13, 18, 22, 27, 31] 5

def z180K30ProjectiveD4ULeaf12KeysPilotV97 : List Nat := [64740]

theorem z180_k30_projective_d4_u_leaf_12_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf12IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf12TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_12_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf12TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf12KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_12_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf12KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
