import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 275: residue 5, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf275IndicesPilotV97 : List Nat :=
  [756, 902, 755, 901, 754]

def z180K30ProjectiveD6ULeaf275SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf275IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf275TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12, 17, 18] [23, 24, 29, 30, 35] 1).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_275_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf275SourcePilotV97 =
      z180K30ProjectiveD6ULeaf275TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
