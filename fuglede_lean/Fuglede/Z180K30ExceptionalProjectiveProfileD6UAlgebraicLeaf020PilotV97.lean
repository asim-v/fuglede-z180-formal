import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 020: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf020IndicesPilotV97 : List Nat :=
  [546, 876, 545, 875, 544, 128, 543, 542, 874, 541]

def z180K30ProjectiveD6ULeaf020SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf020IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf020TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12] [19, 24, 25, 30, 31] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_020_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf020SourcePilotV97 =
      z180K30ProjectiveD6ULeaf020TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
