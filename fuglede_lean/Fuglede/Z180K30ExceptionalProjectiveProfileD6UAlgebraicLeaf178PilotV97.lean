import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 178: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf178IndicesPilotV97 : List Nat :=
  [2068, 1866, 2067, 2066, 2272, 2065, 1865, 2064, 1864, 2063]

def z180K30ProjectiveD6ULeaf178SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf178IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf178TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 3, 6, 12] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_178_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf178SourcePilotV97 =
      z180K30ProjectiveD6ULeaf178TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
