import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 131: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf131IndicesPilotV97 : List Nat :=
  [2257, 2305, 2256, 2304, 2255, 2030, 2254, 2253, 2303, 2252]

def z180K30ProjectiveD6ULeaf131SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf131IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf131TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12, 18] [21, 24, 27, 30, 33] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_131_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf131SourcePilotV97 =
      z180K30ProjectiveD6ULeaf131TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
