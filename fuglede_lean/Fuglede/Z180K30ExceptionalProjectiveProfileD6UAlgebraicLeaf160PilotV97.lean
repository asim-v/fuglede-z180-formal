import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 160: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf160IndicesPilotV97 : List Nat :=
  [2138, 1935, 2137, 1934, 2136, 2279, 2135, 2134, 1933, 2133]

def z180K30ProjectiveD6ULeaf160SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf160IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf160TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 3, 15] [21, 24, 27, 30, 33] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_160_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf160SourcePilotV97 =
      z180K30ProjectiveD6ULeaf160TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
