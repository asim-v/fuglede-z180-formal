import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 266: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf266IndicesPilotV97 : List Nat :=
  [349, 796, 348, 347, 795, 346, 794, 345, 793, 344]

def z180K30ProjectiveD6ULeaf266SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf266IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf266TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 11, 12, 17] [23, 24, 29, 30, 35] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_266_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf266SourcePilotV97 =
      z180K30ProjectiveD6ULeaf266TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
