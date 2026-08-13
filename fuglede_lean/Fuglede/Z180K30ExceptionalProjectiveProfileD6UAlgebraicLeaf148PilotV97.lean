import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 148: residue 3, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf148IndicesPilotV97 : List Nat :=
  [2181, 1971, 2180, 2179, 2286, 2178, 1970, 2177, 1969, 2176]

def z180K30ProjectiveD6ULeaf148SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf148IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf148TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12, 15] [21, 24, 27, 30, 33] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_148_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf148SourcePilotV97 =
      z180K30ProjectiveD6ULeaf148TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
