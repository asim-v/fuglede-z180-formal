import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf 084: residue 2, size 9. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf084IndicesPilotV97 : List Nat :=
  [1795, 1462, 1794, 1793, 1792, 1461, 1791, 1460, 1790]

def z180K30ProjectiveD6ULeaf084SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf084IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf084TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    [0, 6, 12, 18] [20, 24, 26, 30, 32] 2).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_084_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf084SourcePilotV97 =
      z180K30ProjectiveD6ULeaf084TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
