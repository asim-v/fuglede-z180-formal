import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 194: residue 4, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf194IndicesPilotV97 : List Nat :=
  [1760, 1844, 1759, 1843, 1758, 1308, 1757, 1756, 1842, 1755]

def z180K30ProjectiveD6ULeaf194SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf194IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf194TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 12, 18] [22, 24, 28, 30, 34] 3).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_194_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf194SourcePilotV97 =
      z180K30ProjectiveD6ULeaf194TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
