import Fuglede.Z180K18M6DPSemanticBase
import Fuglede.Z180K18M6DPSemanticPhi2
import Fuglede.Z180K18M6DPSemanticPhi12
import Fuglede.Z180K18M6DPSemanticPhi18
import Fuglede.Z180K18M6DPSemanticPhi36
import Fuglede.Z180K18M6Phi45Semantic

/-!
# Sharded semantic realization of the residual `m = 6` DP families

The projection construction, three balance blocks, and four remainder
families are elaborated independently.  This module only dispatches the
seven excluded orders and preserves the public endpoint `z180_k18_m6_dp`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The four canonical DP families close all seven non-pattern exclusions
in the `m = 6` envelope. -/
theorem z180_k18_m6_dp : Z180K18M6DPEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq hqzero
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  have d : Z180K18M6DPBaseData b := by
    simpa only [b] using
      (z180_k18_m6_dp_baseData hSpec hcard hcore hdefect)
  simp only [z180K18M6DPExcludedOrders, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hprojected : cyclotomic 2 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 2) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 2 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    apply z180_k18_m6_dp_close2 b d
    refine ⟨0, ?_⟩
    have hz := projection36_phi2_parity_balance b hindicator
    simpa [z180K18ProjectionPhi2R0] using hz
  · have hmod2 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 2) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    obtain ⟨k2, hk2⟩ :=
      projection36CyclotomicRemainderCoeff_eq_five_mul b hmod2 0
    apply z180_k18_m6_dp_close2 b d
    refine ⟨k2, ?_⟩
    rw [← projection36_phi2_remainderCoeff_eq b]
    exact hk2
  · have hprojected : cyclotomic 12 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 12) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 12 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi12_count12_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    rcases hraw with ⟨hr0, hr1, hr2, hr3⟩
    apply z180_k18_m6_dp_close12 b d
    exact ⟨0, 0, 0, 0,
      by simpa [Z180K12HighOrder.projection36Phi12R0] using hr0,
      by simpa [Z180K12HighOrder.projection36Phi12R1] using hr1,
      by simpa [Z180K12HighOrder.projection36Phi12R2] using hr2,
      by simpa [Z180K12HighOrder.projection36Phi12R3] using hr3⟩
  · have hprojected : cyclotomic 18 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 18) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 18 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi18_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    apply z180_k18_m6_dp_close18 b d
    simpa only [Z180K12HighOrder.projection36Phi18R0,
      Z180K12HighOrder.projection36Phi18R1,
      Z180K12HighOrder.projection36Phi18R2,
      Z180K12HighOrder.projection36Phi18R3,
      Z180K12HighOrder.projection36Phi18R4,
      Z180K12HighOrder.projection36Phi18R5] using hraw
  · have hprojected : cyclotomic 36 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 36) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi36_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    apply z180_k18_m6_dp_close36 b d
    simpa only [Z180K12HighOrder.projection36Phi36R0,
      Z180K12HighOrder.projection36Phi36R1,
      Z180K12HighOrder.projection36Phi36R2,
      Z180K12HighOrder.projection36Phi36R3,
      Z180K12HighOrder.projection36Phi36R4,
      Z180K12HighOrder.projection36Phi36R5,
      Z180K12HighOrder.projection36Phi36R6,
      Z180K12HighOrder.projection36Phi36R7,
      Z180K12HighOrder.projection36Phi36R8,
      Z180K12HighOrder.projection36Phi36R9,
      Z180K12HighOrder.projection36Phi36R10,
      Z180K12HighOrder.projection36Phi36R11] using hraw
  · have hmod12 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 12) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact z180_k18_m6_dp_close12 b d
      (Z180K12HighOrder.projection36_phi12_five_multipliers_high b hmod12)
  · have hmod18 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 18) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact z180_k18_m6_dp_close18 b d
      (Z180K12HighOrder.projection36_phi18_remainders_zero_of_mod_five_dvd_high
        b d.lo d.hi hmod18)

/-- Public `m = 6` envelope assembled from the closed DP and `Phi_45`
frontiers. -/
theorem z180_k18_m6_envelope : Z180K18M6EnvelopeInterface :=
  z180_k18_m6_envelope_of_dp_phi45
    z180_k18_m6_dp z180_k18_m6_phi45_envelope

#print axioms z180_k18_m6_dp
#print axioms z180_k18_m6_envelope

end Fuglede
