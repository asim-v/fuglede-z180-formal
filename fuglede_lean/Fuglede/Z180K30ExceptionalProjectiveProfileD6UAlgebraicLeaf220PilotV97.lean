import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 220: residue 4, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf220IndicesPilotV97 : List Nat :=
  [1648]

def z180K30ProjectiveD6ULeaf220SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf220IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf220TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 10, 12, 16, 18] [22, 24, 28, 30, 34] 0).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_220_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf220SourcePilotV97 =
      z180K30ProjectiveD6ULeaf220TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
