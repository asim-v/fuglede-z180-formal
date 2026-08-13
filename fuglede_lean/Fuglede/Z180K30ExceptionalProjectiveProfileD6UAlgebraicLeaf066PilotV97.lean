import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 066: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf066IndicesPilotV97 : List Nat :=
  [1116, 1542, 1115, 1541, 1114, 1540, 1113, 1112, 1539, 1111]

def z180K30ProjectiveD6ULeaf066SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf066IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf066TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 14, 18] [20, 24, 26, 30, 32] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_066_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf066SourcePilotV97 =
      z180K30ProjectiveD6ULeaf066TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
