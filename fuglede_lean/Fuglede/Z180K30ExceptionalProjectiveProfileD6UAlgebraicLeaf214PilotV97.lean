import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 214: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf214IndicesPilotV97 : List Nat :=
  [1671, 1240, 1670, 1669, 1822, 1668, 1239, 1667, 1238, 1666]

def z180K30ProjectiveD6ULeaf214SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf214IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf214TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 10, 18] [22, 24, 28, 30, 34] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_214_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf214SourcePilotV97 =
      z180K30ProjectiveD6ULeaf214TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
