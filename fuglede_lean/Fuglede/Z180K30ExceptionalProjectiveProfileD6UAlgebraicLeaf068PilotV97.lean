import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 068: residue 2, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf068IndicesPilotV97 : List Nat :=
  [1535, 1808, 1534, 1807, 1533, 1108, 1532, 1531, 1806, 1530]

def z180K30ProjectiveD6ULeaf068SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf068IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf068TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12, 18] [20, 24, 26, 30, 32] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_068_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf068SourcePilotV97 =
      z180K30ProjectiveD6ULeaf068TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
