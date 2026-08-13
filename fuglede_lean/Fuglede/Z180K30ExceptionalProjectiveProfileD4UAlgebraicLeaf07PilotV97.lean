import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U bounded literal bridge leaf 07, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4ULeaf07IndicesPilotV97 : List Nat := [17, 84, 16, 83, 15, 82, 14, 13, 81, 12]

def z180K30ProjectiveD4ULeaf07TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    [0, 2, 9] [11, 18, 20, 27, 29] 3

def z180K30ProjectiveD4ULeaf07KeysPilotV97 : List Nat := [22593, 19855, 19596, 19594, 10272, 10013, 10011, 9939, 9937, 9930]

theorem z180_k30_projective_d4_u_leaf_07_bridge_pilot_v97 :
    z180K30ProjectiveD4ULeaf07IndicesPilotV97.map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveD4ULeaf07TargetPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_07_keys_pilot_v97 :
    z180K30ProjectiveD4ULeaf07TargetPilotV97.map normalizedProjectiveRawSetKeyV89 =
      z180K30ProjectiveD4ULeaf07KeysPilotV97 := by
  decide

theorem z180_k30_projective_d4_u_leaf_07_keys_nodup_pilot_v97 :
    z180K30ProjectiveD4ULeaf07KeysPilotV97.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
