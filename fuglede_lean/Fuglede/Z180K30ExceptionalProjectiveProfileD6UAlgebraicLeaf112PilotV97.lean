import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 112: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf112IndicesPilotV97 : List Nat :=
  [1358, 956, 1357, 1356, 1776, 1355, 955, 1354, 954, 1353]

def z180K30ProjectiveD6ULeaf112SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf112IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf112TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 2, 6, 18] [20, 24, 26, 30, 32] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_112_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf112SourcePilotV97 =
      z180K30ProjectiveD6ULeaf112TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
