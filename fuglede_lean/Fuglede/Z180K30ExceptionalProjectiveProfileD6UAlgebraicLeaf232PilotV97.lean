import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 232: residue 4, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf232IndicesPilotV97 : List Nat :=
  [1599, 1176, 1598, 1175, 1597]

def z180K30ProjectiveD6ULeaf232SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf232IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf232TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 4, 10, 16, 18] [22, 24, 28, 30, 34] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_232_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf232SourcePilotV97 =
      z180K30ProjectiveD6ULeaf232TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
