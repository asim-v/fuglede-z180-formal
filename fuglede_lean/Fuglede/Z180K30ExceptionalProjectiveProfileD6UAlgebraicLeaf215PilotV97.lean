import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 215: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf215IndicesPilotV97 : List Nat :=
  [1237, 1665, 1236, 1235, 1664, 1234, 1663, 1233, 1662, 1232]

def z180K30ProjectiveD6ULeaf215SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf215IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf215TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 10, 16] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_215_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf215SourcePilotV97 =
      z180K30ProjectiveD6ULeaf215TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
