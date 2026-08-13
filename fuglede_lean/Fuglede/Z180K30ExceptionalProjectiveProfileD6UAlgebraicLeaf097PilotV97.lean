import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 097: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf097IndicesPilotV97 : List Nat :=
  [1416, 1013, 1415, 1012, 1414, 1782, 1413, 1412, 1011, 1411]

def z180K30ProjectiveD6ULeaf097SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf097IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf097TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 2, 14] [20, 24, 26, 30, 32] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_097_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf097SourcePilotV97 =
      z180K30ProjectiveD6ULeaf097TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
