import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 083: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf083IndicesPilotV97 : List Nat :=
  [1468, 1798, 1467, 1797, 1466, 1050, 1465, 1464, 1796, 1463]

def z180K30ProjectiveD6ULeaf083SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf083IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf083TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12] [20, 24, 26, 30, 32] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_083_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf083SourcePilotV97 =
      z180K30ProjectiveD6ULeaf083TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
