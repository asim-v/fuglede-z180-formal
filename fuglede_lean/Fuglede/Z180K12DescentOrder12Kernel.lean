import Fuglede.Z180K12DescentMixedKernelInterfaces
import Fuglede.Z180K12DescentDirectCommon
import Fuglede.Z180K12DescentOrder12Converse
import Fuglede.Z180K12M6HighOrderCount12Adapter
import Fuglede.Z180K12M6Order60PairKernel

/-! # Direct exclusion of base order twelve at cardinality twelve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

/-- A `Phi_60/Phi_12` defect cannot occur once the projection to `ZMod 36`
is injective.  The order-two/order-four spectral transforms split the twelve
projected points into four classes of mass three.  The two small pair kernels
then force all four characteristic-five `Phi_12` remainders to vanish. -/
theorem z180_k12_descent_order12_kernel :
    Z180K12DescentOrder12Kernel := by
  intro A hcard hinj htransform2 htransform4 hhigh hlow
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  rcases z180_k12_descent_projection_indicator_data
      hcard hinj htransform2 htransform4 with
    ⟨hloIndicatorRaw, _hhiIndicatorRaw, hmod4Raw⟩
  have hloIndicator : ∀ i, 0 ≤ b i := by
    simpa only [b] using hloIndicatorRaw
  have hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3 := by
    simpa only [b] using hmod4Raw
  have hmodFiveRaw := z180_k12_descent_high_to_projected_mod_five
    (A := A) (m := 12) (by norm_num) (by norm_num) hhigh
  have hmodFive : cyclotomic 12 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5)) := by
    simpa only [b] using hmodFiveRaw
  obtain ⟨t0, t1, t2, t3, ht0, ht1, ht2, ht3⟩ :=
    projection36_phi12_five_multipliers_high b hmodFive
  rcases count12_mod4_high b hmod4 with ⟨hc0, hc1, hc2, hc3⟩
  obtain ⟨hz0Raw, hz2Raw⟩ := order60_pair_remainders_zero
    (projection36Count12 b 0) (projection36Count12 b 4)
    (projection36Count12 b 8) (projection36Count12 b 2)
    (projection36Count12 b 6) (projection36Count12 b 10) t0 t2
    (count12_nonneg_high b hloIndicator 0)
    (count12_nonneg_high b hloIndicator 4)
    (count12_nonneg_high b hloIndicator 8)
    (count12_nonneg_high b hloIndicator 2)
    (count12_nonneg_high b hloIndicator 6)
    (count12_nonneg_high b hloIndicator 10)
    hc0 hc2 ht0 ht2
  obtain ⟨hz1Raw, hz3Raw⟩ := order60_pair_remainders_zero
    (projection36Count12 b 1) (projection36Count12 b 5)
    (projection36Count12 b 9) (projection36Count12 b 3)
    (projection36Count12 b 7) (projection36Count12 b 11) t1 t3
    (count12_nonneg_high b hloIndicator 1)
    (count12_nonneg_high b hloIndicator 5)
    (count12_nonneg_high b hloIndicator 9)
    (count12_nonneg_high b hloIndicator 3)
    (count12_nonneg_high b hloIndicator 7)
    (count12_nonneg_high b hloIndicator 11)
    hc1 hc3 ht1 ht3
  have hz0 : projection36Phi12R0 b = 0 := by
    simpa only [projection36Phi12R0] using hz0Raw
  have hz1 : projection36Phi12R1 b = 0 := by
    simpa only [projection36Phi12R1] using hz1Raw
  have hz2 : projection36Phi12R2 b = 0 := by
    simpa only [projection36Phi12R2] using hz2Raw
  have hz3 : projection36Phi12R3 b = 0 := by
    simpa only [projection36Phi12R3] using hz3Raw
  have hprojectedB :=
    cyclotomic_twelve_dvd_projection36Indicator_of_remainders_zero_direct
      b ⟨hz0, hz1, hz2, hz3⟩
  have hprojected : cyclotomic 12 Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    simpa only [b] using hprojectedB
  exact z180_k12_descent_contradiction_of_projected_divisor
    (A := A) (m := 12) (by norm_num) hlow hprojected

#print axioms z180_k12_descent_order12_kernel

end Z180K12HighOrder

end Fuglede
