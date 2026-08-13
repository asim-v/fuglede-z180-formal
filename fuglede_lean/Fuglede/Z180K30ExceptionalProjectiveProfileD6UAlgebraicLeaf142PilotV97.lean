import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 142: residue 3, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf142IndicesPilotV97 : List Nat :=
  [2209, 1984, 2208, 1983, 2207]

def z180K30ProjectiveD6ULeaf142SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf142IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf142TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6] [21, 24, 27, 30, 33] 4).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_142_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf142SourcePilotV97 =
      z180K30ProjectiveD6ULeaf142TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
