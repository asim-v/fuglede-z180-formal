import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 288: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf288IndicesPilotV97 : List Nat :=
  [282, 709, 281, 708, 280, 707, 279, 278, 706, 277]

def z180K30ProjectiveD6ULeaf288SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf288IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf288TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 5, 12] [23, 24, 29, 30, 35] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_288_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf288SourcePilotV97 =
      z180K30ProjectiveD6ULeaf288TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
