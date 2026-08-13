import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 151: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf151IndicesPilotV97 : List Nat :=
  [2168, 1962, 2167, 2166, 2283, 2165, 1961, 2164, 1960, 2163]

def z180K30ProjectiveD6ULeaf151SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf151IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf151TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 9, 18] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_151_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf151SourcePilotV97 =
      z180K30ProjectiveD6ULeaf151TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
