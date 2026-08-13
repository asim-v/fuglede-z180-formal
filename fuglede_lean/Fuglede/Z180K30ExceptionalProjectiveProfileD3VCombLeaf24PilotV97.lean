import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 24: offset 196, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf24IndicesPilotV97 : List Nat :=
  [35, 105, 163, 145, 199, 227, 287, 337, 364, 354]

def z180K30ProjectiveD3VCombLeaf24SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf24IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf24TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 6, 9] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf24_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf24SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf24TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
