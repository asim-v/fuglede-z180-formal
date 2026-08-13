import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 06, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf06IndicesPilotV97 : List Nat := [20, 86, 19, 85, 18]

def z180K30ProjectiveD4ULeaf06TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 2] [11, 18, 20, 27, 29] 4

def z180K30ProjectiveD4ULeaf06KeysPilotV97 : List Nat := [19823, 58378, 55640, 55381, 55379]

theorem z180_k30_projective_d4_u_leaf_06_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf06IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf06TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_06_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf06TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf06KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_06_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf06KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
