import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 05: offset 26, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf05IndicesPilotV97 : List Nat :=
  [153, 215, 239, 251, 275, 299, 311, 323, 250, 110]

def z180K30ProjectiveD3VCombLeaf05SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf05IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf05TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 12, 18] [21, 24, 27, 30, 33] 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf05_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf05SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf05TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
