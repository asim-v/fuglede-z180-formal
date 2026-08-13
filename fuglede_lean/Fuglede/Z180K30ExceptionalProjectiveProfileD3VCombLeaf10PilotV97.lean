import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 10: offset 71, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf10IndicesPilotV97 : List Nat :=
  [151, 297, 397, 296, 370, 410, 422, 434, 440, 235]

def z180K30ProjectiveD3VCombLeaf10SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf10IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf10TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 9, 15] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf10_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf10SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf10TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
