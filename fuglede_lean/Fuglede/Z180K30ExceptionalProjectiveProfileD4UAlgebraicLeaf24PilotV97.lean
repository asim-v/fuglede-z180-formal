import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 24, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf24IndicesPilotV97 : List Nat := [59]

def z180K30ProjectiveD4ULeaf24TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0] [16, 18, 25, 27, 34] 5

def z180K30ProjectiveD4ULeaf24KeysPilotV97 : List Nat := [56527]

theorem z180_k30_projective_d4_u_leaf_24_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf24IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf24TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_24_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf24TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf24KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_24_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf24KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
