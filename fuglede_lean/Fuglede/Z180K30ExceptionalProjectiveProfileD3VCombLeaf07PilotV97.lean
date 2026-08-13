import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 07: offset 46, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf07IndicesPilotV97 : List Nat :=
  [374, 358, 273, 272, 214, 190, 177, 152, 86, 51]

def z180K30ProjectiveD3VCombLeaf07SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf07IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf07TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 12, 15, 18] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf07_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf07SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf07TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
