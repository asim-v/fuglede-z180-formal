import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 17, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf17IndicesPilotV97 : List Nat := [107, 46, 106, 45, 105]

def z180K30ProjectiveD4ULeaf17TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 9] [14, 18, 23, 27, 32] 4

def z180K30ProjectiveD4ULeaf17KeysPilotV97 : List Nat := [38860, 32811, 25966, 25818, 25813]

theorem z180_k30_projective_d4_u_leaf_17_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf17IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf17TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_17_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf17TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf17KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_17_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf17KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
