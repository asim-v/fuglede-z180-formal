import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 041: residue 1, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf041IndicesPilotV97 : List Nat :=
  [61, 462, 60, 59, 461, 58, 460, 57, 459, 56]

def z180K30ProjectiveD6ULeaf041SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf041IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf041TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 1, 7, 18] [19, 24, 25, 30, 31] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_041_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf041SourcePilotV97 =
      z180K30ProjectiveD6ULeaf041TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
