import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 06: offset 36, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf06IndicesPilotV97 : List Nat :=
  [178, 274, 347, 322, 359, 371, 298, 346, 238, 202]

def z180K30ProjectiveD3VCombLeaf06SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf06IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf06TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 12, 15] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf06_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf06SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf06TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
