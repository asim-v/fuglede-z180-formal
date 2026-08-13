import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 50: offset 398, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf50IndicesPilotV97 : List Nat :=
  [25, 95, 193, 157, 217, 325, 135, 277, 360, 348]

def z180K30ProjectiveD3VCombLeaf50SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf50IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf50TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 15] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf50_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf50SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf50TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
