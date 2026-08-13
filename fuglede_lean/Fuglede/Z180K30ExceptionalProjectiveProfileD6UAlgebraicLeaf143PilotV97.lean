import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 143: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf143IndicesPilotV97 : List Nat :=
  [2206, 2299, 2205, 2298, 2204, 1982, 2203, 2202, 2297, 2201]

def z180K30ProjectiveD6ULeaf143SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf143IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf143TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 18] [21, 24, 27, 30, 33] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_143_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf143SourcePilotV97 =
      z180K30ProjectiveD6ULeaf143TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
