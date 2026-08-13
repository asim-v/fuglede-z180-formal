import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 00: offset 0, size 1. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf00IndicesPilotV97 : List Nat :=
  [5]

def z180K30ProjectiveD3VCombLeaf00SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf00IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf00TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0] [21, 24, 27, 30, 33] 5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf00_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf00SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf00TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
