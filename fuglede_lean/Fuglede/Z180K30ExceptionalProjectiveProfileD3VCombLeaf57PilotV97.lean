import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 57: offset 444, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf57IndicesPilotV97 : List Nat :=
  [21, 91, 156, 132, 120]

def z180K30ProjectiveD3VCombLeaf57SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf57IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf57TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 9, 18] [21, 24, 27, 30, 33] 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf57_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf57SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf57TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
