import Fuglede.Z180K12M6Order20LevelDefs
import Mathlib.Tactic

/-!
# Equal order-six remainders on fifth-coordinate levels
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem cyclotomic_dvd_fifthLevelMask_sub_of_fourier_eq_order20
    (A : Finset (ZMod 180)) (u : CRT180) (c c' : ZMod 5) (m : Nat)
    (hm : 0 < m)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (heq : z180FiveLevelFourierSum A u c =
      z180FiveLevelFourierSum A u c') :
    cyclotomic m Int ∣
      maskPolynomial 180 (z180K12Order20FifthLevel A c) -
        maskPolynomial 180 (z180K12Order20FifthLevel A c') := by
  have hprimitive : IsPrimitiveRoot
      (ZMod.stdAddChar (fromCRT180 u)) m := by
    simpa [horder] using isPrimitiveRoot_stdAddChar (fromCRT180 u)
  rw [cyclotomic_dvd_iff_aeval_primitive hm hprimitive]
  rw [map_sub, aeval_maskPolynomial_stdAddChar,
    aeval_maskPolynomial_stdAddChar]
  rw [← z180K12Order20_fiveLevelFourierSum_eq_fourierSum,
    ← z180K12Order20_fiveLevelFourierSum_eq_fourierSum]
  exact sub_eq_zero.mpr heq

private theorem cyclotomic_dvd_projection36Mask_sub_of_mask_sub_order20
    {m : Nat} (hm36 : m ∣ 36)
    (S T : Finset (ZMod 180))
    (hsub : cyclotomic m Int ∣
      maskPolynomial 180 S - maskPolynomial 180 T) :
    cyclotomic m Int ∣ z180Projection36Mask S - z180Projection36Mask T := by
  have hcyclo36 : cyclotomic m Int ∣
      (X : Polynomial Int) ^ 36 - 1 :=
    (cyclotomic.dvd_X_pow_sub_one m Int).trans
      (dvd_pow_sub_one_of_dvd hm36)
  have hS : cyclotomic m Int ∣
      maskPolynomial 180 S - z180Projection36Mask S :=
    hcyclo36.trans (X_pow_36_sub_one_dvd_mask_sub_projection S)
  have hT : cyclotomic m Int ∣
      maskPolynomial 180 T - z180Projection36Mask T :=
    hcyclo36.trans (X_pow_36_sub_one_dvd_mask_sub_projection T)
  have hbridge : cyclotomic m Int ∣
      (maskPolynomial 180 S - maskPolynomial 180 T) -
        (z180Projection36Mask S - z180Projection36Mask T) := by
    have h := dvd_sub hS hT
    convert h using 1 <;> ring
  have h := dvd_sub hsub hbridge
  convert h using 1 <;> ring

/-- `Phi_30` makes the two projected level masks congruent modulo `Phi_6`.
This is the exact integral version of equality of their complex level sums. -/
theorem z180_k12_order20_level_phi6_sub_dvd
    (A : Finset (ZMod 180))
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (c c' : ZMod 5) :
    cyclotomic 6 Int ∣
      projection36IndicatorMask (z180K12Order20LevelIndicator A c) -
        projection36IndicatorMask (z180K12Order20LevelIndicator A c') := by
  have heq := z180_phi30_defect_fiveLevelSums_eq A h30 c c'
  have hfull := cyclotomic_dvd_fifthLevelMask_sub_of_fourier_eq_order20
    A z180OrderSixBaseFrequency c c' 6 (by norm_num)
      z180OrderSixBaseFrequency_order heq
  have hprojected := cyclotomic_dvd_projection36Mask_sub_of_mask_sub_order20
    (m := 6) (by norm_num)
      (z180K12Order20FifthLevel A c)
      (z180K12Order20FifthLevel A c') hfull
  simpa [z180K12Order20LevelIndicator,
    projection36IndicatorMask_z180K12ProjectionIndicator] using hprojected

#print axioms z180_k12_order20_level_phi6_sub_dvd

end Fuglede
