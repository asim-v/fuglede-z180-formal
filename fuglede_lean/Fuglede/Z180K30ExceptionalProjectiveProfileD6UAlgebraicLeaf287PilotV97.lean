import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 287: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf287IndicesPilotV97 : List Nat :=
  [288, 713, 287, 286, 712, 285, 711, 284, 710, 283]

def z180K30ProjectiveD6ULeaf287SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf287IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf287TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 5, 17, 18] [23, 24, 29, 30, 35] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_287_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf287SourcePilotV97 =
      z180K30ProjectiveD6ULeaf287TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
