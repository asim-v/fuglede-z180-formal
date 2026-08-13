import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97

/-! Nat-only index bucket 19, size 7. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_index_bucket_b19_pilot_v97 :
    ((List.range 462).filter
      (z180K30ProjectiveD3VIndexPredicatePilotV97 19)).Perm
      (z180K30ProjectiveD3VCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD3VIndexPredicatePilotV97 19)) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
