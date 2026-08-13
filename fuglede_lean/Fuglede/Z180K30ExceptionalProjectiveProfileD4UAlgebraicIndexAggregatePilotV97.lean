import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicIndexB16PilotV97

/-! Structural aggregate of the seventeen bounded D4-U Nat-index buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_index_perm_pilot_v97 :
    (List.range 168).Perm z180K30ProjectiveD4UCanonicalIndicesPilotV97 := by
  have hBuckets :
      ((List.range 17).flatMap fun bucket =>
        (List.range 168).filter
          (z180K30ProjectiveD4UIndexPredicatePilotV97 bucket)).Perm
      ((List.range 17).flatMap fun bucket =>
        z180K30ProjectiveD4UCanonicalIndicesPilotV97.filter
          (z180K30ProjectiveD4UIndexPredicatePilotV97 bucket)) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket <;> first
      | exact z180_k30_projective_d4_u_index_bucket_b00_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b01_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b02_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b03_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b04_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b05_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b06_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b07_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b08_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b09_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b10_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b11_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b12_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b13_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b14_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b15_pilot_v97
      | exact z180_k30_projective_d4_u_index_bucket_b16_pilot_v97
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) 17 (by decide) (List.range 168)
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) 17 (by decide)
    z180K30ProjectiveD4UCanonicalIndicesPilotV97
  exact hSource.symm.trans (hBuckets.trans hTarget)

theorem z180_k30_projective_d4_u_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.length = 168 := by
  rfl

private theorem map_range_getD_eq_self_d4u_pilot
    {alpha : Type} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index => values.getD index fallback) =
      values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d4_u_source_range_pilot_v97 :
    (List.range 168).map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D4USourceGrouped := by
  rw [← z180_k30_projective_d4_u_source_length_pilot_v97]
  exact map_range_getD_eq_self_d4u_pilot
    z180K30ProjectiveCompletenessV97D4USourceGrouped []

theorem z180_k30_projective_d4_u_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.Perm
      z180K30ProjectiveD4UCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d4_u_index_perm_pilot_v97.map
    z180K30ProjectiveD4USourceAtPilotV97
  rw [z180_k30_projective_d4_u_source_range_pilot_v97] at h
  exact h

end Fuglede.Z180K30ExceptionalRawV2
