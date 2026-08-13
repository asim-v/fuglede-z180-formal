import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 129: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf129IndicesPilotV97 : List Nat :=
  [2038, 2264, 2037, 2263, 2036, 2262, 2035, 2034, 2261, 2033]

def z180K30ProjectiveD6ULeaf129SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf129IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf129TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 15, 18] [21, 24, 27, 30, 33] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_129_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf129SourcePilotV97 =
      z180K30ProjectiveD6ULeaf129TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
