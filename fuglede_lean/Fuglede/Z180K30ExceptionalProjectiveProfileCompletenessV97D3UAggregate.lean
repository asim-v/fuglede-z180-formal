import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UB00
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UB01

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_profile_members_complete_v97_d3_u :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.Perm
      normalizedProjectiveUniqueUChoicesV89 3 := by
  have hBuckets :
      (List.range 2).flatMap
          (fun bucket => (z180K30ProjectiveCompletenessV97D3USourceGrouped).filter
            (z180K30ProjectiveCompletenessV97D3UPredicate bucket)) |>.Perm
        ((List.range 2).flatMap
          (fun bucket => (normalizedProjectiveUniqueUChoicesV89 3).filter
            (z180K30ProjectiveCompletenessV97D3UPredicate bucket))) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket
    | 0 => exact z180_k30_projective_profile_completeness_v97_d3_u_b00
    | 1 => exact z180_k30_projective_profile_completeness_v97_d3_u_b01
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 2 (by decide)
    z180K30ProjectiveCompletenessV97D3USourceGrouped
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 2 (by decide)
    (normalizedProjectiveUniqueUChoicesV89 3)
  exact hSource.symm.trans (hBuckets.trans hTarget)

end Fuglede.Z180K30ExceptionalRawV2
