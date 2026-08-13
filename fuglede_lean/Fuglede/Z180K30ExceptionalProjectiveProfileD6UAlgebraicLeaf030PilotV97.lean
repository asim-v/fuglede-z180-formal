import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 030: residue 1, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf030IndicesPilotV97 : List Nat :=
  [103, 503, 102, 502, 101]

def z180K30ProjectiveD6ULeaf030SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf030IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf030TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 7, 12, 13] [19, 24, 25, 30, 31] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_030_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf030SourcePilotV97 =
      z180K30ProjectiveD6ULeaf030TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
