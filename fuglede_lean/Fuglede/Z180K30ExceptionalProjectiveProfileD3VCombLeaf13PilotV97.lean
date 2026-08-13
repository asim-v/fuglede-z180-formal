import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf 13: offset 101, size 10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf13IndicesPilotV97 : List Nat :=
  [269, 455, 445, 431, 409, 396, 340, 395, 383, 188]

def z180K30ProjectiveD3VCombLeaf13SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf13IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf13TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    [0, 9, 12, 18] [21, 24, 27, 30, 33] 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf13_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf13SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf13TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
