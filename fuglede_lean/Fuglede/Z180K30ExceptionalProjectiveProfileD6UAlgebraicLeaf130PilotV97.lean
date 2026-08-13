import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 130: residue 3, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf130IndicesPilotV97 : List Nat :=
  [2260, 2032, 2259, 2031, 2258]

def z180K30ProjectiveD6ULeaf130SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf130IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf130TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12] [21, 24, 27, 30, 33] 4).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_130_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf130SourcePilotV97 =
      z180K30ProjectiveD6ULeaf130TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
