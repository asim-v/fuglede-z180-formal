import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 076: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf076IndicesPilotV97 : List Nat :=
  [1499, 1074, 1498, 1497, 1803, 1496, 1073, 1495, 1072, 1494]

def z180K30ProjectiveD6ULeaf076SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf076IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf076TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 8, 12, 18] [20, 24, 26, 30, 32] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_076_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf076SourcePilotV97 =
      z180K30ProjectiveD6ULeaf076TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
