import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97

/-! Nat-only index bucket 13, size 8. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_index_bucket_b13_pilot_v97 :
    ((List.range 462).filter
      (z180K30ProjectiveD3VIndexPredicatePilotV97 13)).Perm
      (z180K30ProjectiveD3VCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD3VIndexPredicatePilotV97 13)) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
