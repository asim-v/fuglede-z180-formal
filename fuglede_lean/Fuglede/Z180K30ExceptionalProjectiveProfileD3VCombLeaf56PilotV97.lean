import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 56: offset 434, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf56IndicesPilotV97 : List Nat :=
  [2, 9, 23, 22, 55, 121, 43, 67, 133, 168]

def z180K30ProjectiveD3VCombLeaf56SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf56IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf56TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 9] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf56_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf56SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf56TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
