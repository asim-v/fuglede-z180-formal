import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 294: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf294IndicesPilotV97 : List Nat :=
  [683, 893, 682, 681, 255, 680, 892, 679, 891, 678]

def z180K30ProjectiveD6ULeaf294SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf294IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf294TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 5, 11, 17] [23, 24, 29, 30, 35] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_294_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf294SourcePilotV97 =
      z180K30ProjectiveD6ULeaf294TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
