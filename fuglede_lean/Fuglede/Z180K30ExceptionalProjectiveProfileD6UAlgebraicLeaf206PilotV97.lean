import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 206: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf206IndicesPilotV97 : List Nat :=
  [1709, 1838, 1708, 1837, 1707, 1260, 1706, 1705, 1836, 1704]

def z180K30ProjectiveD6ULeaf206SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf206IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf206TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 18] [22, 24, 28, 30, 34] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_206_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf206SourcePilotV97 =
      z180K30ProjectiveD6ULeaf206TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
