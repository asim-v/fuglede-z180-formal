import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 19, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf19IndicesPilotV97 : List Nat := [41, 102, 40, 101, 39, 100, 38, 37, 99, 36]

def z180K30ProjectiveD4ULeaf19TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 5, 9] [14, 18, 23, 27, 32] 3

def z180K30ProjectiveD4ULeaf19KeysPilotV97 : List Nat := [14380, 7535, 7387, 7382, 2059, 1911, 1906, 1726, 1721, 1717]

theorem z180_k30_projective_d4_u_leaf_19_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf19IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf19TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_19_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf19TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf19KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_19_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf19KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
