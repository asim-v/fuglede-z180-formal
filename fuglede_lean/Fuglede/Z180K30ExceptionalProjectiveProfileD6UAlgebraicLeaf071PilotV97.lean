import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 071: residue 2, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf071IndicesPilotV97 : List Nat :=
  [1098, 1519, 1097, 1518, 1096]

def z180K30ProjectiveD6ULeaf071SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf071IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf071TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 8] [20, 24, 26, 30, 32] 4).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_071_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf071SourcePilotV97 =
      z180K30ProjectiveD6ULeaf071TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
