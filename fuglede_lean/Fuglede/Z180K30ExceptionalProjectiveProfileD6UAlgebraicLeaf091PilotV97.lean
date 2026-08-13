import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 091: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf091IndicesPilotV97 : List Nat :=
  [1434, 1028, 1433, 1432, 1785, 1431, 1027, 1430, 1026, 1429]

def z180K30ProjectiveD6ULeaf091SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf091IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf091TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 8, 12] [20, 24, 26, 30, 32] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_091_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf091SourcePilotV97 =
      z180K30ProjectiveD6ULeaf091TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
