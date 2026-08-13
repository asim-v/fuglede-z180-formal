import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 021: residue 1, size 9. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf021IndicesPilotV97 : List Nat :=
  [873, 540, 872, 871, 870, 539, 869, 538, 868]

def z180K30ProjectiveD6ULeaf021SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf021IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf021TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12, 18] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_021_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf021SourcePilotV97 =
      z180K30ProjectiveD6ULeaf021TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
