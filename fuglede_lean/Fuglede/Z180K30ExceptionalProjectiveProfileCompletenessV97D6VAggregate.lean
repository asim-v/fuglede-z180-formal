import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VB00

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_profile_members_complete_v97_d6_v :
    z180K30ProjectiveCompletenessV97D6VSourceGrouped.Perm
      normalizedProjectiveUniqueVChoicesV89 6 := by
  have hSource00 :
      z180K30ProjectiveCompletenessV97D6VSourceTailB00.Perm z180K30ProjectiveCompletenessV97D6VSourceRemainderB00 := by
    rfl
  have hTarget00 :
      z180K30ProjectiveCompletenessV97D6VTargetTailB00.Perm z180K30ProjectiveCompletenessV97D6VTargetRemainderB00 := by
    rfl
  have hBuckets00 :
      z180K30ProjectiveCompletenessV97D6VSourceTailB00.Perm z180K30ProjectiveCompletenessV97D6VTargetTailB00 := by
    exact z180_k30_projective_profile_completeness_v97_d6_v_b00
  exact hSource00.symm.trans (hBuckets00.trans hTarget00)

end Fuglede.Z180K30ExceptionalRawV2
