import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 223: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf223IndicesPilotV97 : List Nat :=
  [1641, 1213, 1640, 1212, 1639, 1818, 1638, 1637, 1211, 1636]

def z180K30ProjectiveD6ULeaf223SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf223IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf223TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 4, 16] [22, 24, 28, 30, 34] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_223_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf223SourcePilotV97 =
      z180K30ProjectiveD6ULeaf223TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
