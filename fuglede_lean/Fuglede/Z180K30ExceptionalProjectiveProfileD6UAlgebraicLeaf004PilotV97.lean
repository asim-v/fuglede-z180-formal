import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 004: residue 1, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf004IndicesPilotV97 : List Nat :=
  [616, 188, 615, 187, 614]

def z180K30ProjectiveD6ULeaf004SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf004IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf004TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12] [19, 24, 25, 30, 31] 4).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_004_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf004SourcePilotV97 =
      z180K30ProjectiveD6ULeaf004TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
