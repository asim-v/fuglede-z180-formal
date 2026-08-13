import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 44: offset 357, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf44IndicesPilotV97 : List Nat :=
  [29, 97, 159, 195, 219, 327, 183, 376, 387, 326]

def z180K30ProjectiveD3VCombLeaf44SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf44IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf44TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 9, 12] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf44_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf44SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf44TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
