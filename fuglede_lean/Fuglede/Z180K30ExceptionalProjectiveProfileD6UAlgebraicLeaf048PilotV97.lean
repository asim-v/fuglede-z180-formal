import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 048: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf048IndicesPilotV97 : List Nat :=
  [40, 440, 39, 439, 38, 438, 37, 36, 437, 35]

def z180K30ProjectiveD6ULeaf048SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf048IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf048TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 1, 6] [19, 24, 25, 30, 31] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_048_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf048SourcePilotV97 =
      z180K30ProjectiveD6ULeaf048TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
