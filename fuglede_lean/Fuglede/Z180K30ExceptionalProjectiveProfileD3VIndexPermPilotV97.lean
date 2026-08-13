import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB09PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB10PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB11PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB12PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB13PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB14PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB15PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB16PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB17PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB18PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB19PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB20PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB21PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB22PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB23PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB24PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB25PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB26PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB27PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB28PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB29PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB30PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB31PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB32PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB33PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB34PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB35PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB36PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB37PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB38PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB39PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB40PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB41PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB42PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB43PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB44PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB45PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB46PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB47PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB48PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB49PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB50PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB51PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB52PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB53PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB54PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB55PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB56PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB57PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB58PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB59PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB60PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB61PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB62PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermB63PilotV97

/-! Structural aggregate of 64 Nat-only index buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97 :
    (List.range 462).Perm
      z180K30ProjectiveD3VCanonicalIndicesPilotV97 := by
  have hBuckets :
      ((List.range 64).flatMap fun bucket =>
        (List.range 462).filter
          (z180K30ProjectiveD3VIndexPredicatePilotV97 bucket)).Perm
      ((List.range 64).flatMap fun bucket =>
        z180K30ProjectiveD3VCanonicalIndicesPilotV97.filter
          (z180K30ProjectiveD3VIndexPredicatePilotV97 bucket)) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket <;> first
      | exact z180_k30_projective_d3_v_index_bucket_b00_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b01_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b02_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b03_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b04_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b05_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b06_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b07_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b08_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b09_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b10_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b11_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b12_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b13_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b14_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b15_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b16_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b17_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b18_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b19_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b20_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b21_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b22_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b23_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b24_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b25_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b26_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b27_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b28_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b29_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b30_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b31_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b32_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b33_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b34_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b35_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b36_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b37_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b38_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b39_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b40_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b41_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b42_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b43_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b44_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b45_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b46_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b47_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b48_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b49_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b50_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b51_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b52_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b53_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b54_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b55_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b56_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b57_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b58_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b59_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b60_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b61_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b62_pilot_v97
      | exact z180_k30_projective_d3_v_index_bucket_b63_pilot_v97
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) 64 (by decide)
    (List.range 462)
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) 64 (by decide)
    z180K30ProjectiveD3VCanonicalIndicesPilotV97
  exact hSource.symm.trans (hBuckets.trans hTarget)

private theorem map_range_getD_eq_self_pilot_v97
    {alpha : Type} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index =>
      values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d3_v_source_range_pilot_v97 :
    (List.range 462).map z180K30ProjectiveD3VSourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D3VSourceGrouped := by
  rw [← z180_k30_projective_d3_v_source_length_pilot_v97]
  exact map_range_getD_eq_self_pilot_v97
    z180K30ProjectiveCompletenessV97D3VSourceGrouped []

theorem z180_k30_projective_d3_v_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.Perm
      z180K30ProjectiveD3VCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97.map
    z180K30ProjectiveD3VSourceAtPilotV97
  rw [z180_k30_projective_d3_v_source_range_pilot_v97] at h
  exact h

#print axioms z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97
#print axioms z180_k30_projective_d3_v_source_perm_indexed_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
