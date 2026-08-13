import Fuglede.Z180K12M6HighOrderModFive
import Fuglede.Z180K12M6HighOrderProjectionLift
import Mathlib.Tactic

/-!
# Direct semantic adapters for the cardinality-twelve descent

This module contains only the two generic changes of viewpoint used by the
base-order `12`, `18`, and `36` exclusions:

* a `Phi_(5m)` divisor becomes a characteristic-five `Phi_m` divisor of the
  projected indicator mask;
* an integral `Phi_m` divisor of that projected mask lifts back to the
  original mask.

It also derives the zero-one bounds and the modulo-four profile directly from
cardinality, injectivity of the projection, and the exact-order transforms at
orders two and four.  In particular, none of these statements assumes the
`m = 6` defect package.
-/

namespace Fuglede

open Polynomial

namespace Z180K12HighOrder

/-- The genuine projected indicator is zero-one and has four residue classes
of mass three.  This is the part of `z180_k12_m6_prepare` independent of the
`Phi_30/Phi_6` defect. -/
theorem z180_k12_descent_projection_indicator_data
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0) :
    (∀ i : Fin 36, 0 ≤ z180K12ProjectionIndicator A i) ∧
    (∀ i : Fin 36, z180K12ProjectionIndicator A i ≤ 1) ∧
    (
      z180K12ProjectionIndicator A 0 + z180K12ProjectionIndicator A 4 +
          z180K12ProjectionIndicator A 8 + z180K12ProjectionIndicator A 12 +
          z180K12ProjectionIndicator A 16 + z180K12ProjectionIndicator A 20 +
          z180K12ProjectionIndicator A 24 + z180K12ProjectionIndicator A 28 +
          z180K12ProjectionIndicator A 32 = 3 ∧
      z180K12ProjectionIndicator A 1 + z180K12ProjectionIndicator A 5 +
          z180K12ProjectionIndicator A 9 + z180K12ProjectionIndicator A 13 +
          z180K12ProjectionIndicator A 17 + z180K12ProjectionIndicator A 21 +
          z180K12ProjectionIndicator A 25 + z180K12ProjectionIndicator A 29 +
          z180K12ProjectionIndicator A 33 = 3 ∧
      z180K12ProjectionIndicator A 2 + z180K12ProjectionIndicator A 6 +
          z180K12ProjectionIndicator A 10 + z180K12ProjectionIndicator A 14 +
          z180K12ProjectionIndicator A 18 + z180K12ProjectionIndicator A 22 +
          z180K12ProjectionIndicator A 26 + z180K12ProjectionIndicator A 30 +
          z180K12ProjectionIndicator A 34 = 3 ∧
      z180K12ProjectionIndicator A 3 + z180K12ProjectionIndicator A 7 +
          z180K12ProjectionIndicator A 11 + z180K12ProjectionIndicator A 15 +
          z180K12ProjectionIndicator A 19 + z180K12ProjectionIndicator A 23 +
          z180K12ProjectionIndicator A 27 + z180K12ProjectionIndicator A 31 +
          z180K12ProjectionIndicator A 35 = 3) := by
  have hmask2 : cyclotomic 2 Int ∣ maskPolynomial 180 A :=
    z180_cyclotomic_dvd_mask_of_transform_zero
      (A := A) (e := 2) (u := 90) (by norm_num) (by decide) htransform2
  have hmask4 : cyclotomic 4 Int ∣ maskPolynomial 180 A :=
    z180_cyclotomic_dvd_mask_of_transform_zero
      (A := A) (e := 4) (u := 45) (by norm_num) (by decide) htransform4
  have hprojected2 : cyclotomic 2 Int ∣ z180Projection36Mask A :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (m := 2) (by norm_num)).2 hmask2
  have hprojected4 : cyclotomic 4 Int ∣ z180Projection36Mask A :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (m := 4) (by norm_num)).2 hmask4
  have hbmask := projection36IndicatorMask_z180K12ProjectionIndicator A
  have hdiv2 : cyclotomic 2 Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    rw [hbmask]
    exact hprojected2
  have hdiv4 : cyclotomic 4 Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    rw [hbmask]
    exact hprojected4
  have hsum :
      (∑ i : Fin 36, z180K12ProjectionIndicator A i) = 12 := by
    rw [sum_z180K12ProjectionIndicator, hcard]
    norm_num
  exact
    ⟨z180K12ProjectionIndicator_nonneg A,
      z180K12ProjectionIndicator_le_one_of_injOn hinj,
      projection36_mod4_profile
        (z180K12ProjectionIndicator A) hsum hdiv2 hdiv4⟩

/-- Direct `hhigh` adapter.  The public descent interfaces use `m * 5`, while
the characteristic-five theorem is naturally stated with `5 * m`. -/
theorem z180_k12_descent_high_to_projected_mod_five
    {A : Finset (ZMod 180)} {m : Nat}
    (hm5 : ¬ 5 ∣ m) (hm36 : m ∣ 36)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A) :
    cyclotomic m (ZMod 5) ∣
      (projection36IndicatorMask
        (z180K12ProjectionIndicator A)).map
          (Int.castRingHom (ZMod 5)) := by
  apply cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
    hm5 hm36
  simpa [Nat.mul_comm] using hhigh

/-- Direct `hlow` adapter: a projected integral divisor contradicts the
asserted defect downstairs after the standard projection lift. -/
theorem z180_k12_descent_contradiction_of_projected_divisor
    {A : Finset (ZMod 180)} {m : Nat}
    (hm36 : m ∣ 36)
    (hlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A)
    (hprojected : cyclotomic m Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A)) :
    False :=
  hlow (projected_integer_divisor_lifts_high hm36 hprojected)

#print axioms z180_k12_descent_projection_indicator_data
#print axioms z180_k12_descent_high_to_projected_mod_five
#print axioms z180_k12_descent_contradiction_of_projected_divisor

end Z180K12HighOrder

end Fuglede
