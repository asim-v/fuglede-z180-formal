import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 36: offset 287, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf36IndicesPilotV97 : List Nat :=
  [30, 100, 196, 184, 160, 222, 378, 333, 390, 332]

def z180K30ProjectiveD3VCombLeaf36SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf36IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf36TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 12] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf36_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf36SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf36TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
