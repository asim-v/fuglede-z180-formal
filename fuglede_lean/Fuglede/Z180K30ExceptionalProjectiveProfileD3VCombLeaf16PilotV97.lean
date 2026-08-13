import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 16: offset 126, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf16IndicesPilotV97 : List Nat :=
  [15, 118, 107, 83, 63]

def z180K30ProjectiveD3VCombLeaf16SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf16IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf16TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 6] [21, 24, 27, 30, 33] 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf16_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf16SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf16TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
