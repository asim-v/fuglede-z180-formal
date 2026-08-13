import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 09: offset 61, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf09IndicesPilotV97 : List Nat :=
  [166, 237, 386, 310, 345, 398, 385, 344, 236, 165]

def z180K30ProjectiveD3VCombLeaf09SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf09IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf09TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 9, 18] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf09_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf09SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf09TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
