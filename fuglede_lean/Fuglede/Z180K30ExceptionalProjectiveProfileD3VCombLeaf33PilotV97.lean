import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 33: offset 257, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf33IndicesPilotV97 : List Nat :=
  [31, 59, 77, 101, 127, 143, 161, 175, 142, 126]

def z180K30ProjectiveD3VCombLeaf33SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf33IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf33TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 18] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf33_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf33SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf33TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
