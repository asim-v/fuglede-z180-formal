import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 069: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf069IndicesPilotV97 : List Nat :=
  [1107, 1529, 1106, 1528, 1105, 1527, 1104, 1103, 1526, 1102]

def z180K30ProjectiveD6ULeaf069SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf069IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf069TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12, 14] [20, 24, 26, 30, 32] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_069_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf069SourcePilotV97 =
      z180K30ProjectiveD6ULeaf069TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
