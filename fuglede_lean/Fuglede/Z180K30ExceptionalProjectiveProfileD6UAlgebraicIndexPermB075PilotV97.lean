import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Nat-only D6-U index bucket 75; sizes 9/9. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_index_bucket_b075_pilot_v97 :
    ((List.range 2306).filter
      (z180K30ProjectiveD6UIndexPredicatePilotV97 75)).Perm
      (z180K30ProjectiveD6UCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD6UIndexPredicatePilotV97 75)) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
