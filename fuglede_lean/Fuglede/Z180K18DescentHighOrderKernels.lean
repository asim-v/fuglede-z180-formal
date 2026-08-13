import Fuglede.Z180K12M6HighOrderProjectionLift
import Fuglede.Z180K12M6HighOrderRemainders18Shard
import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard

/-!
# Table-free high-order descent exclusions at cardinality eighteen

These two exclusions are independent of the cardinality-twelve preparation.
They use only injectivity of projection to `ZMod 36`, the high cyclotomic
factor supplied by a five-factor defect, and the missing low factor.
-/

namespace Fuglede

namespace Z180K18HighOrder

open Polynomial

/-- An injective projection cannot have a `Phi_90`/not-`Phi_18` defect. -/
theorem z180_k18_descent_order18_kernel
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (hhigh : cyclotomic 90 Int ∣ maskPolynomial 180 A)
    (hlow : ¬ cyclotomic 18 Int ∣ maskPolynomial 180 A) :
    False := by
  have hmodFive : cyclotomic 18 (ZMod 5) ∣
      (projection36IndicatorMask
        (z180K12ProjectionIndicator A)).map
          (Int.castRingHom (ZMod 5)) := by
    apply cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 18) (by norm_num) (by norm_num)
    simpa using hhigh
  have hremainders :=
    Z180K12HighOrder.projection36_phi18_remainders_zero_of_mod_five_dvd_high
      (z180K12ProjectionIndicator A)
      (z180K12ProjectionIndicator_nonneg A)
      (z180K12ProjectionIndicator_le_one_of_injOn hinj)
      hmodFive
  have hprojected :=
    Z180K12HighOrder.cyclotomic_eighteen_dvd_projection36Indicator_of_remainders_zero_high
      (z180K12ProjectionIndicator A) hremainders
  apply hlow
  exact Z180K12HighOrder.projected_integer_divisor_lifts_high
    (A := A) (m := 18) (by norm_num) hprojected

/-- An injective projection cannot have a `Phi_180`/not-`Phi_36` defect. -/
theorem z180_k18_descent_order36_kernel
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (hhigh : cyclotomic 180 Int ∣ maskPolynomial 180 A)
    (hlow : ¬ cyclotomic 36 Int ∣ maskPolynomial 180 A) :
    False := by
  have hmodFive : cyclotomic 36 (ZMod 5) ∣
      (projection36IndicatorMask
        (z180K12ProjectionIndicator A)).map
          (Int.castRingHom (ZMod 5)) := by
    apply cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 36) (by norm_num) (by norm_num)
    simpa using hhigh
  have hremainders :=
    Z180K12HighOrder.projection36_phi36_remainders_zero_of_mod_five_dvd_high
      (z180K12ProjectionIndicator A)
      (z180K12ProjectionIndicator_nonneg A)
      (z180K12ProjectionIndicator_le_one_of_injOn hinj)
      hmodFive
  have hprojected :=
    Z180K12HighOrder.cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero_high
      (z180K12ProjectionIndicator A) hremainders
  apply hlow
  exact Z180K12HighOrder.projected_integer_divisor_lifts_high
    (A := A) (m := 36) (by norm_num) hprojected

#print axioms z180_k18_descent_order18_kernel
#print axioms z180_k18_descent_order36_kernel

end Z180K18HighOrder

end Fuglede
