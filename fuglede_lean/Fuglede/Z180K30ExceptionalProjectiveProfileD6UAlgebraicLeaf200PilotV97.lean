import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 200: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf200IndicesPilotV97 : List Nat :=
  [1286, 1732, 1285, 1284, 1731, 1283, 1730, 1282, 1729, 1281]

def z180K30ProjectiveD6ULeaf200SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf200IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf200TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 10, 16, 18] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_200_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf200SourcePilotV97 =
      z180K30ProjectiveD6ULeaf200TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
