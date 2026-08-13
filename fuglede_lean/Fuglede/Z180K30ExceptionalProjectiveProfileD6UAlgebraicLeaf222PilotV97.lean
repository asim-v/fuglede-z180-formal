import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 222: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf222IndicesPilotV97 : List Nat :=
  [1219, 1645, 1218, 1644, 1217, 1643, 1216, 1215, 1642, 1214]

def z180K30ProjectiveD6ULeaf222SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf222IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf222TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 4, 18] [22, 24, 28, 30, 34] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_222_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf222SourcePilotV97 =
      z180K30ProjectiveD6ULeaf222TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
