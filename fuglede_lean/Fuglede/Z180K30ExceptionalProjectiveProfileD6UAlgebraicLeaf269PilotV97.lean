import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 269: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf269IndicesPilotV97 : List Nat :=
  [787, 916, 786, 915, 785, 338, 784, 783, 914, 782]

def z180K30ProjectiveD6ULeaf269SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf269IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf269TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 18] [23, 24, 29, 30, 35] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_269_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf269SourcePilotV97 =
      z180K30ProjectiveD6ULeaf269TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
