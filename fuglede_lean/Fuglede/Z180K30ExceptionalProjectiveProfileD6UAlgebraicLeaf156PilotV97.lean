import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 156: residue 3, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf156IndicesPilotV97 : List Nat :=
  [1947, 2147, 1946, 2146, 1945]

def z180K30ProjectiveD6ULeaf156SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf156IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf156TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 9, 12, 15] [21, 24, 27, 30, 33] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_156_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf156SourcePilotV97 =
      z180K30ProjectiveD6ULeaf156TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
