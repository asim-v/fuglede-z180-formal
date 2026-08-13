import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 177: residue 3, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf177IndicesPilotV97 : List Nat :=
  [1869, 2070, 1868, 2069, 1867]

def z180K30ProjectiveD6ULeaf177SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf177IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf177TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 3, 6, 15, 18] [21, 24, 27, 30, 33] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_177_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf177SourcePilotV97 =
      z180K30ProjectiveD6ULeaf177TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
