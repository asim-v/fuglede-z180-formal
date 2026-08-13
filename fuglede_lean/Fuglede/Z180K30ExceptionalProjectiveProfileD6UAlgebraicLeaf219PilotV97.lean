import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 219: residue 4, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf219IndicesPilotV97 : List Nat :=
  [1225, 1650, 1224, 1649, 1223]

def z180K30ProjectiveD6ULeaf219SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf219IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf219TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 10, 12, 16] [22, 24, 28, 30, 34] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_219_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf219SourcePilotV97 =
      z180K30ProjectiveD6ULeaf219TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
