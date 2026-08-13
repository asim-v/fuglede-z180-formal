import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 245: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf245IndicesPilotV97 : List Nat :=
  [1138, 1559, 1137, 1136, 1558, 1135, 1557, 1134, 1556, 1133]

def z180K30ProjectiveD6ULeaf245SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf245IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf245TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 4, 6, 10] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_245_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf245SourcePilotV97 =
      z180K30ProjectiveD6ULeaf245TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
