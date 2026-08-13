import Fuglede.Z180K12DescentMixedKernelInterfaces
import Fuglede.Z180K12DescentDirectCommon
import Fuglede.Z180K12DescentOrder3Arithmetic
import Fuglede.Z180K12DescentOrder3Converse
import Fuglede.Z180K12M6HighOrderCount12Adapter
import Fuglede.Z180K12M6HighOrderRemainders3_12Shard

/-! # Direct exclusion of base order three at cardinality twelve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

/-- A `Phi_15/Phi_3` defect cannot occur.  Characteristic five makes the
two projected `Phi_3` remainders multiples of five; the four mass-three
classes force both multiples to be zero, and the integral divisor lifts. -/
theorem z180_k12_descent_order3_kernel :
    Z180K12DescentOrderKernel 3 := by
  intro A hcard hinj htransform2 htransform4 hhigh hlow
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  rcases z180_k12_descent_projection_indicator_data
      hcard hinj htransform2 htransform4 with
    ⟨hloRaw, _hhiRaw, hmod4Raw⟩
  have hlo : ∀ i, 0 ≤ b i := by
    simpa only [b] using hloRaw
  have hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3 := by
    simpa only [b] using hmod4Raw
  have hmodFiveRaw := z180_k12_descent_high_to_projected_mod_five
    (A := A) (m := 3) (by norm_num) (by norm_num) hhigh
  have hmodFive : cyclotomic 3 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5)) := by
    simpa only [b] using hmodFiveRaw
  obtain ⟨k0, k1, hr0, hr1⟩ :=
    projection36_phi3_five_multipliers_high b hmodFive
  rcases count12_mod4_high b hmod4 with ⟨hm0, hm1, hm2, hm3⟩
  have hr0Count :
      projection36Count12 b 0 - projection36Count12 b 2 +
        projection36Count12 b 3 - projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 +
        projection36Count12 b 9 - projection36Count12 b 11 = 5 * k0 := by
    simpa only [projection36Phi3R0] using hr0
  have hr1Count :
      projection36Count12 b 1 - projection36Count12 b 2 +
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 - projection36Count12 b 8 +
        projection36Count12 b 10 - projection36Count12 b 11 = 5 * k1 := by
    simpa only [projection36Phi3R1] using hr1
  have hzCount := descent_order3_five_multiples_zero
    (projection36Count12 b 0) (projection36Count12 b 1)
    (projection36Count12 b 2) (projection36Count12 b 3)
    (projection36Count12 b 4) (projection36Count12 b 5)
    (projection36Count12 b 6) (projection36Count12 b 7)
    (projection36Count12 b 8) (projection36Count12 b 9)
    (projection36Count12 b 10) (projection36Count12 b 11) k0 k1
    (count12_nonneg_high b hlo 0) (count12_nonneg_high b hlo 1)
    (count12_nonneg_high b hlo 2) (count12_nonneg_high b hlo 3)
    (count12_nonneg_high b hlo 4) (count12_nonneg_high b hlo 5)
    (count12_nonneg_high b hlo 6) (count12_nonneg_high b hlo 7)
    (count12_nonneg_high b hlo 8) (count12_nonneg_high b hlo 9)
    (count12_nonneg_high b hlo 10) (count12_nonneg_high b hlo 11)
    hm0 hm1 hm2 hm3 hr0Count hr1Count
  have hz : projection36Phi3R0 b = 0 ∧ projection36Phi3R1 b = 0 := by
    simpa only [projection36Phi3R0, projection36Phi3R1] using hzCount
  have hprojectedB :=
    cyclotomic_three_dvd_projection36Indicator_of_remainders_zero_direct b hz
  have hprojected : cyclotomic 3 Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    simpa only [b] using hprojectedB
  exact z180_k12_descent_contradiction_of_projected_divisor
    (A := A) (m := 3) (by norm_num) hlow hprojected

#print axioms z180_k12_descent_order3_kernel

end Z180K12HighOrder

end Fuglede
