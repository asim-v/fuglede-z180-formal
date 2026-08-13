import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 196: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf196IndicesPilotV97 : List Nat :=
  [1750, 1301, 1749, 1748, 1841, 1747, 1300, 1746, 1299, 1745]

def z180K30ProjectiveD6ULeaf196SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf196IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf196TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12, 16, 18] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_196_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf196SourcePilotV97 =
      z180K30ProjectiveD6ULeaf196TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
