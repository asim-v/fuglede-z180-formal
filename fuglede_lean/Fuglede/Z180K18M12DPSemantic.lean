import Fuglede.Z180K18M12DPSemanticBase
import Fuglede.Z180K18M12DPSemanticPhi4
import Fuglede.Z180K18M12DPSemanticPhi6
import Fuglede.Z180K18M12DPSemanticPhi18
import Fuglede.Z180K18M12DPSemanticPhi36

/-!
# Sharded semantic realization of the residual `m = 12` DP families

The expensive projection construction and the four paired-remainder families
are elaborated in independent leaves.  This module only dispatches the six
orders and preserves the public endpoint `z180_k18_m12_dp`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The four canonical DP families close the six non-pattern residual
orders in the `m = 12` envelope. -/
theorem z180_k18_m12_dp : Z180K18M12DPEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq hqzero
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  have d : Z180K18M12DPBaseData b := by
    simpa only [b] using
      (z180_k18_m12_dp_baseData hSpec hcard hcore hdefect)
  simp only [z180K18M12DPExcludedOrders, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · have hprojected : cyclotomic 4 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 4) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 4 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    obtain ⟨hr0, hr1⟩ :=
      projection36_phi4_count12_remainders_order20 b hindicator
    apply z180_k18_m12_dp_close4 b d
    exact ⟨0, 0,
      by simpa [z180K18ProjectionPhi4R0] using hr0,
      by simpa [z180K18ProjectionPhi4R1] using hr1⟩
  · have hprojected : cyclotomic 6 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 6) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 6 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    exact z180_k18_m12_dp_close6 b d
      ((projection36_phi6_dvd_iff_remainders_zero b).1 hindicator)
  · have hprojected : cyclotomic 18 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 18) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 18 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi18_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    apply z180_k18_m12_dp_close18 b d
    simpa only [Z180K12HighOrder.projection36Phi18R0,
      Z180K12HighOrder.projection36Phi18R1,
      Z180K12HighOrder.projection36Phi18R2,
      Z180K12HighOrder.projection36Phi18R3,
      Z180K12HighOrder.projection36Phi18R4,
      Z180K12HighOrder.projection36Phi18R5] using hraw
  · have hmod4 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 4) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact z180_k18_m12_dp_close4 b d
      (projection36_phi4_five_multipliers b hmod4)
  · have hprojected : cyclotomic 36 Int ∣ z180Projection36Mask A :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 36) (by norm_num)).2 hqzero
    have hindicator : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
      simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
        using hprojected
    have hraw := projection36_phi36_remainders b
      (by simpa [projection36IndicatorMask] using hindicator)
    apply z180_k18_m12_dp_close36 b d
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
  · have hmod36 :=
      cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
        (A := A) (m := 36) (by norm_num) (by norm_num)
          (by simpa using hqzero)
    exact z180_k18_m12_dp_close36 b d
      (Z180K12HighOrder.projection36_phi36_remainders_zero_of_mod_five_dvd_high
        b d.lo d.hi hmod36)

#print axioms z180_k18_m12_dp

end Fuglede
