import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 135: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf135IndicesPilotV97 : List Nat :=
  [2017, 2239, 2016, 2238, 2015, 2237, 2014, 2013, 2236, 2012]

def z180K30ProjectiveD6ULeaf135SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf135IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf135TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 9, 18] [21, 24, 27, 30, 33] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_135_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf135SourcePilotV97 =
      z180K30ProjectiveD6ULeaf135TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
