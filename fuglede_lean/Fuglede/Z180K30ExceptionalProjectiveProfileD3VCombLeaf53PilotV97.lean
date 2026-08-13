import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 53: offset 423, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf53IndicesPilotV97 : List Nat :=
  [56, 240, 216, 204, 134]

def z180K30ProjectiveD3VCombLeaf53SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf53IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf53TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 12, 18] [21, 24, 27, 30, 33] 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf53_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf53SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf53TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
