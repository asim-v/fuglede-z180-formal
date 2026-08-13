import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 119: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf119IndicesPilotV97 : List Nat :=
  [938, 1334, 937, 936, 1333, 935, 1332, 934, 1331, 933]

def z180K30ProjectiveD6ULeaf119SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf119IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf119TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 2, 6, 8] [20, 24, 26, 30, 32] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_119_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf119SourcePilotV97 =
      z180K30ProjectiveD6ULeaf119TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
