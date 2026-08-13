import Fuglede.Z180K18M12HighOrderArithmetic
import Fuglede.Z180FiveLevelFourier
import Fuglede.Z180K12M6SemanticCommon
import Mathlib.Tactic

/-!
# Fifth-level Fourier bridge for the `k = 18`, `m = 12` pair geometry

`Phi_10`, `Phi_30`, and `Phi_90` make the order-two Fourier coordinate of
every fifth-coordinate level agree at all nine frequencies of `ZMod 9`.
The integral inversion is supplied by `Z180K18M12HighOrderArithmetic`.

This module stops at the exact level-profile conclusion.  Turning that
profile into two named points of each modulo-nine fibre is a finite-set
combinatorial adapter and is deliberately kept separate.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 0

/-- One fifth-coordinate level of a set in `ZMod 180`. -/
noncomputable def z180K18M12FifthLevel
    (A : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 180) :=
  A.filter fun x => crt180FifthCoord (toCRT180 x) = c

/-- Projected integral indicator of one fifth-coordinate level. -/
noncomputable def z180K18M12LevelIndicator
    (A : Finset (ZMod 180)) (c : ZMod 5) : Fin 36 → Int :=
  z180K12ProjectionIndicator (z180K18M12FifthLevel A c)

/-- The exact conclusion of the high-order Fourier argument. -/
def Z180K18M12LevelSignedProfilesZero
    (A : Finset (ZMod 180)) : Prop :=
  ∀ c : ZMod 5, ∀ r : ZMod 9,
    z180K18M12SignedNineFiber (z180K18M12LevelIndicator A c) r = 0

/-- The five levels partition every projected coordinate. -/
theorem sum_z180K18M12LevelIndicator
    (A : Finset (ZMod 180)) (i : Fin 36) :
    (∑ c : ZMod 5, z180K18M12LevelIndicator A c i) =
      z180K12ProjectionIndicator A i := by
  classical
  change (∑ c : ZMod 5,
      ((z180Projection36Occupancy
        (A.filter fun x => crt180FifthCoord (toCRT180 x) = c) i : Nat) : Int)) =
    ((z180Projection36Occupancy A i : Nat) : Int)
  norm_cast
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter
    (A.filter fun x => z180Projection36Coordinate x = i)
      (Finset.univ : Finset (ZMod 5))
      (fun x => crt180FifthCoord (toCRT180 x))
  simpa [z180Projection36Occupancy, Finset.filter_filter,
    and_left_comm, and_comm, and_assoc] using hpartition

/-- Level Fourier sums are ordinary Fourier sums of the filtered level. -/
theorem z180K18M12_fiveLevelFourierSum_eq_fourierSum
    (A : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) :
    z180FiveLevelFourierSum A u c =
      fourierSum (z180K18M12FifthLevel A c) (fromCRT180 u) := by
  rw [← z180StandardCRTFourierSum_eq_fourierSum]
  rfl

/-- Equality of two level Fourier sums at an exact-order frequency gives the
corresponding cyclotomic divisor of the difference of their full masks. -/
theorem z180_k18_m12_cyclotomic_dvd_levelMask_sub_of_fourier_eq
    (A : Finset (ZMod 180)) (u : CRT180) (c c' : ZMod 5) (m : Nat)
    (hm : 0 < m)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (heq : z180FiveLevelFourierSum A u c =
      z180FiveLevelFourierSum A u c') :
    cyclotomic m Int ∣
      maskPolynomial 180 (z180K18M12FifthLevel A c) -
        maskPolynomial 180 (z180K18M12FifthLevel A c') := by
  have hprimitive : IsPrimitiveRoot
      (ZMod.stdAddChar (fromCRT180 u)) m := by
    simpa [horder] using isPrimitiveRoot_stdAddChar (fromCRT180 u)
  rw [cyclotomic_dvd_iff_aeval_primitive hm hprimitive]
  rw [map_sub, aeval_maskPolynomial_stdAddChar,
    aeval_maskPolynomial_stdAddChar]
  rw [← z180K18M12_fiveLevelFourierSum_eq_fourierSum,
    ← z180K18M12_fiveLevelFourierSum_eq_fourierSum]
  exact sub_eq_zero.mpr heq

/-- Project a cyclotomic divisor of a mask difference from 180 to 36. -/
theorem z180_k18_m12_cyclotomic_dvd_projection36Mask_sub_of_mask_sub
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

/-- Base frequency of exact order two with zero fifth coordinate. -/
noncomputable def z180K18M12OrderTwoBaseFrequency : CRT180 :=
  toCRT180 (90 : ZMod 180)

/-- Base frequency of exact order eighteen with zero fifth coordinate. -/
noncomputable def z180K18M12OrderEighteenBaseFrequency : CRT180 :=
  toCRT180 (10 : ZMod 180)

@[simp] theorem z180K18M12OrderTwoBaseFrequency_fifthCoord :
    crt180FifthCoord z180K18M12OrderTwoBaseFrequency = 0 := by
  change (ZMod.cast (90 : ZMod 180) : ZMod 5) = 0
  decide

@[simp] theorem z180K18M12OrderTwoBaseFrequency_order :
    frequencyOrder 180 (fromCRT180 z180K18M12OrderTwoBaseFrequency) = 2 := by
  rw [z180K18M12OrderTwoBaseFrequency, fromCRT180_toCRT180]
  decide

@[simp] theorem z180K18M12OrderEighteenBaseFrequency_fifthCoord :
    crt180FifthCoord z180K18M12OrderEighteenBaseFrequency = 0 := by
  change (ZMod.cast (10 : ZMod 180) : ZMod 5) = 0
  decide

@[simp] theorem z180K18M12OrderEighteenBaseFrequency_order :
    frequencyOrder 180
      (fromCRT180 z180K18M12OrderEighteenBaseFrequency) = 18 := by
  rw [z180K18M12OrderEighteenBaseFrequency, fromCRT180_toCRT180]
  decide

/-- Generic `Phi_(5m)` bridge for the difference of two projected fifth
levels. -/
theorem z180_k18_m12_level_sub_dvd_of_five_mul
    (A : Finset (ZMod 180)) (u : CRT180) (c c' : ZMod 5) (m : Nat)
    (hm : 0 < m) (hm36 : m ∣ 36)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A) :
    cyclotomic m Int ∣
      projection36IndicatorMask (z180K18M12LevelIndicator A c) -
        projection36IndicatorMask (z180K18M12LevelIndicator A c') := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    A u m hu horder hhigh c c'
  have hfull := z180_k18_m12_cyclotomic_dvd_levelMask_sub_of_fourier_eq
    A u c c' m hm horder heq
  have hprojected :=
    z180_k18_m12_cyclotomic_dvd_projection36Mask_sub_of_mask_sub
      hm36 (z180K18M12FifthLevel A c)
        (z180K18M12FifthLevel A c') hfull
  simpa [z180K18M12LevelIndicator,
    projection36IndicatorMask_z180K12ProjectionIndicator] using hprojected

/-- `Phi_10`, `Phi_30`, and `Phi_90` make the alternating projected profile
independent of the fifth-coordinate level. -/
theorem z180_k18_m12_level_signed_profiles_eq
    (A : Finset (ZMod 180))
    (h10 : cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : cyclotomic 90 Int ∣ maskPolynomial 180 A) :
    ∀ c c' : ZMod 5, ∀ r : ZMod 9,
      z180K18M12SignedNineFiber (z180K18M12LevelIndicator A c) r =
        z180K18M12SignedNineFiber (z180K18M12LevelIndicator A c') r := by
  intro c c'
  have h2 := z180_k18_m12_level_sub_dvd_of_five_mul
    A z180K18M12OrderTwoBaseFrequency c c' 2 (by norm_num) (by norm_num)
      z180K18M12OrderTwoBaseFrequency_fifthCoord
      z180K18M12OrderTwoBaseFrequency_order (by simpa using h10)
  have h6 := z180_k18_m12_level_sub_dvd_of_five_mul
    A z180OrderSixBaseFrequency c c' 6 (by norm_num) (by norm_num)
      z180OrderSixBaseFrequency_fifthCoord z180OrderSixBaseFrequency_order
      (by simpa using h30)
  have h18 := z180_k18_m12_level_sub_dvd_of_five_mul
    A z180K18M12OrderEighteenBaseFrequency c c' 18
      (by norm_num) (by norm_num)
      z180K18M12OrderEighteenBaseFrequency_fifthCoord
      z180K18M12OrderEighteenBaseFrequency_order (by simpa using h90)
  exact z180_k18_m12_signedNineFiber_eq_of_sub_dvd
    (z180K18M12LevelIndicator A c)
    (z180K18M12LevelIndicator A c') h2 h6 h18

#print axioms sum_z180K18M12LevelIndicator
#print axioms z180_k18_m12_level_sub_dvd_of_five_mul
#print axioms z180_k18_m12_level_signed_profiles_eq

end Fuglede
