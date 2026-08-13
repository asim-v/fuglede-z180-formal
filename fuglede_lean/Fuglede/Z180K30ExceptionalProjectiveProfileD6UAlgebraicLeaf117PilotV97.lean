import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 117: residue 2, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf117IndicesPilotV97 : List Nat :=
  [941, 1337, 940, 1336, 939]

def z180K30ProjectiveD6ULeaf117SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf117IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf117TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 2, 6, 12, 14] [20, 24, 26, 30, 32] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_117_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf117SourcePilotV97 =
      z180K30ProjectiveD6ULeaf117TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
