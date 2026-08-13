import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 038: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf038IndicesPilotV97 : List Nat :=
  [73, 474, 72, 71, 473, 70, 472, 69, 471, 68]

def z180K30ProjectiveD6ULeaf038SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf038IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf038TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 1, 12, 13] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_038_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf038SourcePilotV97 =
      z180K30ProjectiveD6ULeaf038TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
