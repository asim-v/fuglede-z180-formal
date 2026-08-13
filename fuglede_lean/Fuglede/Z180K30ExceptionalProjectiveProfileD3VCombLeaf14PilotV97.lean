import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 14: offset 111, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf14IndicesPilotV97 : List Nat :=
  [176, 268, 356, 339, 369, 338, 320, 294, 234, 200]

def z180K30ProjectiveD3VCombLeaf14SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf14IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf14TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 9, 12, 15] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf14_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf14SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf14TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
