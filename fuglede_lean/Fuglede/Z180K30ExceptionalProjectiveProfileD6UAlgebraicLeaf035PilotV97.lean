import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 035: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf035IndicesPilotV97 : List Nat :=
  [88, 488, 87, 86, 487, 85, 486, 84, 485, 83]

def z180K30ProjectiveD6ULeaf035SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf035IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf035TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 1, 13, 18] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_035_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf035SourcePilotV97 =
      z180K30ProjectiveD6ULeaf035TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
