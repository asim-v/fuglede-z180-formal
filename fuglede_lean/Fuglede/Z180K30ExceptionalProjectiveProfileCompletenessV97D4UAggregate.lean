import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB00
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB01
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB02
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB03
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB04
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB05
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB06
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB07
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB08
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB09
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB10
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB11
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB12
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB13
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB14
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB15
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB16
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB17
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB18
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB19
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB20
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB21
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB22
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB23
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB24
import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UB25

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_profile_members_complete_v97_d4_u :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.Perm
      normalizedProjectiveUniqueUChoicesV89 4 := by
  have hBuckets :
      (List.range 26).flatMap
          (fun bucket => (z180K30ProjectiveCompletenessV97D4USourceGrouped).filter
            (z180K30ProjectiveCompletenessV97D4UPredicate bucket)) |>.Perm
        ((List.range 26).flatMap
          (fun bucket => (normalizedProjectiveUniqueUChoicesV89 4).filter
            (z180K30ProjectiveCompletenessV97D4UPredicate bucket))) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket
    | 0 => exact z180_k30_projective_profile_completeness_v97_d4_u_b00
    | 1 => exact z180_k30_projective_profile_completeness_v97_d4_u_b01
    | 2 => exact z180_k30_projective_profile_completeness_v97_d4_u_b02
    | 3 => exact z180_k30_projective_profile_completeness_v97_d4_u_b03
    | 4 => exact z180_k30_projective_profile_completeness_v97_d4_u_b04
    | 5 => exact z180_k30_projective_profile_completeness_v97_d4_u_b05
    | 6 => exact z180_k30_projective_profile_completeness_v97_d4_u_b06
    | 7 => exact z180_k30_projective_profile_completeness_v97_d4_u_b07
    | 8 => exact z180_k30_projective_profile_completeness_v97_d4_u_b08
    | 9 => exact z180_k30_projective_profile_completeness_v97_d4_u_b09
    | 10 => exact z180_k30_projective_profile_completeness_v97_d4_u_b10
    | 11 => exact z180_k30_projective_profile_completeness_v97_d4_u_b11
    | 12 => exact z180_k30_projective_profile_completeness_v97_d4_u_b12
    | 13 => exact z180_k30_projective_profile_completeness_v97_d4_u_b13
    | 14 => exact z180_k30_projective_profile_completeness_v97_d4_u_b14
    | 15 => exact z180_k30_projective_profile_completeness_v97_d4_u_b15
    | 16 => exact z180_k30_projective_profile_completeness_v97_d4_u_b16
    | 17 => exact z180_k30_projective_profile_completeness_v97_d4_u_b17
    | 18 => exact z180_k30_projective_profile_completeness_v97_d4_u_b18
    | 19 => exact z180_k30_projective_profile_completeness_v97_d4_u_b19
    | 20 => exact z180_k30_projective_profile_completeness_v97_d4_u_b20
    | 21 => exact z180_k30_projective_profile_completeness_v97_d4_u_b21
    | 22 => exact z180_k30_projective_profile_completeness_v97_d4_u_b22
    | 23 => exact z180_k30_projective_profile_completeness_v97_d4_u_b23
    | 24 => exact z180_k30_projective_profile_completeness_v97_d4_u_b24
    | 25 => exact z180_k30_projective_profile_completeness_v97_d4_u_b25
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 26 (by decide)
    z180K30ProjectiveCompletenessV97D4USourceGrouped
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 26 (by decide)
    (normalizedProjectiveUniqueUChoicesV89 4)
  exact hSource.symm.trans (hBuckets.trans hTarget)

end Fuglede.Z180K30ExceptionalRawV2
