import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 261: residue 5, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf261IndicesPilotV97 : List Nat :=
  [373, 820, 372, 819, 371, 818, 370, 369, 817, 368]

def z180K30ProjectiveD6ULeaf261SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf261IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf261TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 11, 18] [23, 24, 29, 30, 35] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_261_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf261SourcePilotV97 =
      z180K30ProjectiveD6ULeaf261TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
