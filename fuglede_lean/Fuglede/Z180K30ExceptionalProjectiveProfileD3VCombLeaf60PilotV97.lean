import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 60: offset 455, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf60IndicesPilotV97 : List Nat :=
  [1, 7, 19, 42, 18]

def z180K30ProjectiveD3VCombLeaf60SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf60IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf60TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 9, 12] [21, 24, 27, 30, 33] 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf60_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf60SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf60TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
