import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 23, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf23IndicesPilotV97 : List Nat := [143, 162, 142, 161, 141, 160, 140, 139, 159, 138]

def z180K30ProjectiveD4ULeaf23TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 6, 9] [15, 18, 24, 27, 33] 3

def z180K30ProjectiveD4ULeaf23KeysPilotV97 : List Nat := [55323, 47109, 46998, 46992, 43002, 42891, 42885, 42669, 42663, 42660]

theorem z180_k30_projective_d4_u_leaf_23_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf23IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf23TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_23_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf23TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf23KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_23_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf23KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
