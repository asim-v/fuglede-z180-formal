import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 147: residue 3, size 9. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf147IndicesPilotV97 : List Nat :=
  [2292, 2184, 2291, 2290, 2289, 2183, 2288, 2182, 2287]

def z180K30ProjectiveD6ULeaf147SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf147IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf147TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12, 18] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_147_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf147SourcePilotV97 =
      z180K30ProjectiveD6ULeaf147TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
