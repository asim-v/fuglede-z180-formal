import Fuglede.Z180K12M6Order20LevelDefs
import Mathlib.Tactic

/-!
# The order-four zero on every fifth-coordinate level
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem cyclotomic_dvd_fifthLevelMask_of_fourier_zero_order20
    (A : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) (m : Nat)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hzero : z180FiveLevelFourierSum A u c = 0) :
    cyclotomic m Int ∣ maskPolynomial 180
      (z180K12Order20FifthLevel A c) := by
  have hfourier : fourierSum (z180K12Order20FifthLevel A c)
      (fromCRT180 u) = 0 := by
    rw [← z180K12Order20_fiveLevelFourierSum_eq_fourierSum]
    exact hzero
  have hcyclo : CyclotomicZero 180
      (z180K12Order20FifthLevel A c) (fromCRT180 u) :=
    (cyclotomicZero_iff_fourierSum_zero _ _).2 hfourier
  unfold CyclotomicZero at hcyclo
  rwa [horder] at hcyclo

/-- `Phi_20` and the already-forced global `Phi_4` zero imply a `Phi_4`
zero on every fifth-coordinate level. -/
theorem z180_k12_order20_level_phi4_dvd
    (A : Finset (ZMod 180))
    (h20 : cyclotomic 20 Int ∣ maskPolynomial 180 A)
    (h4 : cyclotomic 4 Int ∣ maskPolynomial 180 A)
    (c : ZMod 5) :
    cyclotomic 4 Int ∣ projection36IndicatorMask
      (z180K12Order20LevelIndicator A c) := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    A z180OrderFourBaseFrequency 4
      z180OrderFourBaseFrequency_fifthCoord
      z180OrderFourBaseFrequency_order (by simpa using h20)
  have hbaseCyclo : CyclotomicZero 180 A
      (fromCRT180 z180OrderFourBaseFrequency) := by
    unfold CyclotomicZero
    rwa [z180OrderFourBaseFrequency_order]
  have hbaseFourier : fourierSum A
      (fromCRT180 z180OrderFourBaseFrequency) = 0 :=
    (cyclotomicZero_iff_fourierSum_zero _ _).1 hbaseCyclo
  have hsum :
      (∑ d : ZMod 5,
        z180FiveLevelFourierSum A z180OrderFourBaseFrequency d) = 0 := by
    rw [sum_z180FiveLevelFourierSum_eq,
      z180StandardCRTFourierSum_eq_fourierSum]
    exact hbaseFourier
  rw [sum_zmod_five_explicit_order20] at hsum
  rw [heq 0 c, heq 1 c, heq 2 c, heq 3 c, heq 4 c] at hsum
  have hc : z180FiveLevelFourierSum A z180OrderFourBaseFrequency c = 0 := by
    have hfive : (5 : ℂ) *
        z180FiveLevelFourierSum A z180OrderFourBaseFrequency c = 0 := by
      linear_combination hsum
    exact (mul_eq_zero.mp hfive).resolve_left (by norm_num)
  have hlevel : cyclotomic 4 Int ∣ maskPolynomial 180
      (z180K12Order20FifthLevel A c) :=
    cyclotomic_dvd_fifthLevelMask_of_fourier_zero_order20 A
      z180OrderFourBaseFrequency c 4
      z180OrderFourBaseFrequency_order hc
  have hprojected : cyclotomic 4 Int ∣
      z180Projection36Mask (z180K12Order20FifthLevel A c) :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask (by norm_num)).2 hlevel
  simpa [z180K12Order20LevelIndicator,
    projection36IndicatorMask_z180K12ProjectionIndicator] using hprojected

#print axioms z180_k12_order20_level_phi4_dvd

end Fuglede
