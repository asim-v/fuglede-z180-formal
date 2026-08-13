import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 026: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf026IndicesPilotV97 : List Nat :=
  [115, 518, 114, 113, 517, 112, 516, 111, 515, 110]

def z180K30ProjectiveD6ULeaf026SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf026IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf026TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 7, 13] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_026_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf026SourcePilotV97 =
      z180K30ProjectiveD6ULeaf026TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
