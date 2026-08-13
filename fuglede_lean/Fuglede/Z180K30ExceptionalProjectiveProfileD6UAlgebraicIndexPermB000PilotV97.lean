import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Nat-only D6-U index bucket 0; sizes 10/10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_index_bucket_b000_pilot_v97 :
    ((List.range 2306).filter
      (z180K30ProjectiveD6UIndexPredicatePilotV97 0)).Perm
      (z180K30ProjectiveD6UCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD6UIndexPredicatePilotV97 0)) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
