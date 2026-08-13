import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 19: offset 151, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf19IndicesPilotV97 : List Nat :=
  [266, 453, 430, 444, 408, 394, 355, 368, 290, 148]

def z180K30ProjectiveD3VCombLeaf19SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf19IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf19TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 6, 15, 18] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf19_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf19SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf19TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
