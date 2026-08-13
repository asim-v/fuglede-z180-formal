import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 140: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf140IndicesPilotV97 : List Nat :=
  [1993, 2215, 1992, 1991, 2214, 1990, 2213, 1989, 2212, 1988]

def z180K30ProjectiveD6ULeaf140SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf140IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf140TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 9, 12, 15] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_140_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf140SourcePilotV97 =
      z180K30ProjectiveD6ULeaf140TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
