import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB00
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB01
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB02
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB03
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB04
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB05
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VB06

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_profile_members_complete_v97_d4_v :
    z180K30ProjectiveCompletenessV97D4VSourceGrouped.Perm
      normalizedProjectiveUniqueVChoicesV89 4 := by
  have hBuckets :
      (List.range 7).flatMap
          (fun bucket => (z180K30ProjectiveCompletenessV97D4VSourceGrouped).filter
            (z180K30ProjectiveCompletenessV97D4VPredicate bucket)) |>.Perm
        ((List.range 7).flatMap
          (fun bucket => (normalizedProjectiveUniqueVChoicesV89 4).filter
            (z180K30ProjectiveCompletenessV97D4VPredicate bucket))) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket
    | 0 => exact z180_k30_projective_profile_completeness_v97_d4_v_b00
    | 1 => exact z180_k30_projective_profile_completeness_v97_d4_v_b01
    | 2 => exact z180_k30_projective_profile_completeness_v97_d4_v_b02
    | 3 => exact z180_k30_projective_profile_completeness_v97_d4_v_b03
    | 4 => exact z180_k30_projective_profile_completeness_v97_d4_v_b04
    | 5 => exact z180_k30_projective_profile_completeness_v97_d4_v_b05
    | 6 => exact z180_k30_projective_profile_completeness_v97_d4_v_b06
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 7 (by decide)
    z180K30ProjectiveCompletenessV97D4VSourceGrouped
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 7 (by decide)
    (normalizedProjectiveUniqueVChoicesV89 4)
  exact hSource.symm.trans (hBuckets.trans hTarget)

end Fuglede.Z180K30ExceptionalRawV2
