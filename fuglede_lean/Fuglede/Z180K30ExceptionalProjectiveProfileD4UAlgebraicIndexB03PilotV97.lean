import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! D4-U Nat-only index bucket 3; source=10, target=10. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_index_bucket_b03_pilot_v97 :
    ((List.range 168).filter
      (z180K30ProjectiveD4UIndexPredicatePilotV97 3)).Perm
      (z180K30ProjectiveD4UCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD4UIndexPredicatePilotV97 3)) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
