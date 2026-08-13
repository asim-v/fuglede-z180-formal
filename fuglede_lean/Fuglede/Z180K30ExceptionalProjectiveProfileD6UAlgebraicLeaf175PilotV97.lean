import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 175: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf175IndicesPilotV97 : List Nat :=
  [2080, 1878, 2079, 2078, 2273, 2077, 1877, 2076, 1876, 2075]

def z180K30ProjectiveD6ULeaf175SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf175IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf175TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 3, 6, 18] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_175_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf175SourcePilotV97 =
      z180K30ProjectiveD6ULeaf175TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
