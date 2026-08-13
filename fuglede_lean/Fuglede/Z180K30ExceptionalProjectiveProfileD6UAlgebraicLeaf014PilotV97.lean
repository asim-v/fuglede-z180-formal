import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 014: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf014IndicesPilotV97 : List Nat :=
  [149, 571, 148, 147, 570, 146, 569, 145, 568, 144]

def z180K30ProjectiveD6ULeaf014SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf014IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf014TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 7, 12, 13] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_014_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf014SourcePilotV97 =
      z180K30ProjectiveD6ULeaf014TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
