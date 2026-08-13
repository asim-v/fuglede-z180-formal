import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 21: offset 171, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf21IndicesPilotV97 : List Nat :=
  [211, 417, 406, 405, 461, 404, 366, 403, 416, 210]

def z180K30ProjectiveD3VCombLeaf21SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf21IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf21TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 6, 12, 18] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf21_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf21SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf21TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
