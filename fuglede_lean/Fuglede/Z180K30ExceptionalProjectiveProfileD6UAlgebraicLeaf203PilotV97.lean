import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 203: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf203IndicesPilotV97 : List Nat :=
  [1271, 1718, 1270, 1269, 1717, 1268, 1716, 1267, 1715, 1266]

def z180K30ProjectiveD6ULeaf203SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf203IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf203TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 10, 12, 16] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_203_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf203SourcePilotV97 =
      z180K30ProjectiveD6ULeaf203TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
