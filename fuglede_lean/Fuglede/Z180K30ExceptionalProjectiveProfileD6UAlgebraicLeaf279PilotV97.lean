import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 279: residue 5, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf279IndicesPilotV97 : List Nat :=
  [309, 739, 308, 738, 307]

def z180K30ProjectiveD6ULeaf279SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf279IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf279TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 11, 17, 18] [23, 24, 29, 30, 35] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_279_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf279SourcePilotV97 =
      z180K30ProjectiveD6ULeaf279TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
