import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 161: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf161IndicesPilotV97 : List Nat :=
  [1932, 2132, 1931, 1930, 2131, 1929, 2130, 1928, 2129, 1927]

def z180K30ProjectiveD6ULeaf161SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf161IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf161TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 3, 15, 18] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_161_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf161SourcePilotV97 =
      z180K30ProjectiveD6ULeaf161TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
