import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 31: offset 251, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf31IndicesPilotV97 : List Nat :=
  [14]

def z180K30ProjectiveD3VCombLeaf31SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf31IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf31TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 6, 9, 12, 15, 18] [21, 24, 27, 30, 33] 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf31_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf31SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf31TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
