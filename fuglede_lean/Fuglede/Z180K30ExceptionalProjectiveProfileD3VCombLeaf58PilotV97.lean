import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 58: offset 449, size 5. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf58IndicesPilotV97 : List Nat :=
  [8, 114, 90, 66, 54]

def z180K30ProjectiveD3VCombLeaf58SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf58IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf58TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 3, 6, 9, 15] [21, 24, 27, 30, 33] 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf58_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf58SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf58TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
