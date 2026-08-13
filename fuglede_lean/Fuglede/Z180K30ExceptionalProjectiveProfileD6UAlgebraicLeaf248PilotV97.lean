import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 248: residue 4, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf248IndicesPilotV97 : List Nat :=
  [1127]

def z180K30ProjectiveD6ULeaf248SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf248IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf248TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 4, 6, 10, 16, 18] [22, 24, 28, 30, 34] 0).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_248_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf248SourcePilotV97 =
      z180K30ProjectiveD6ULeaf248TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
