import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 48: offset 378, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf48IndicesPilotV97 : List Nat :=
  [3, 11, 27, 46, 26, 57, 71, 123, 137, 171]

def z180K30ProjectiveD3VCombLeaf48SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf48IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf48TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf48_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf48SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf48TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
