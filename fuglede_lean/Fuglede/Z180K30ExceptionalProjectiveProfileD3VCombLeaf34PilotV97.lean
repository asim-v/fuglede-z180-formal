import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 34: offset 267, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf34IndicesPilotV97 : List Nat :=
  [48, 76, 185, 197, 141, 207, 223, 263, 283, 317]

def z180K30ProjectiveD3VCombLeaf34SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf34IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf34TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 15] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf34_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf34SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf34TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
