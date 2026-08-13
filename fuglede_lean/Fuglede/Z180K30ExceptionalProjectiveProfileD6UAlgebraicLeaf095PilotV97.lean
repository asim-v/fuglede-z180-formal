import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 095: residue 2, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf095IndicesPilotV97 : List Nat :=
  [1022, 1422, 1021, 1421, 1020]

def z180K30ProjectiveD6ULeaf095SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf095IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf095TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 2] [20, 24, 26, 30, 32] 4).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_095_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf095SourcePilotV97 =
      z180K30ProjectiveD6ULeaf095TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
