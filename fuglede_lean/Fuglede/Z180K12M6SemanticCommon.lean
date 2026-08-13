import Fuglede.Z180K12EnvelopeBridge
import Fuglede.Z180K12Projection36Phi6
import Mathlib.Tactic

/-!
# Semantic preparation of the cardinality-twelve `m = 6` indicators

This module turns a genuine subset of `ZMod 180` into the exact zero-one
indicator package consumed by the compact order 9, 18, and 36 kernels.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

noncomputable def z180K12ProjectionIndicator
    (A : Finset (ZMod 180)) (i : Fin 36) : Int :=
  (z180Projection36Occupancy A i : Int)

theorem projection36IndicatorMask_z180K12ProjectionIndicator
    (A : Finset (ZMod 180)) :
    projection36IndicatorMask (z180K12ProjectionIndicator A) =
      z180Projection36Mask A := by
  rw [z180Projection36Mask_eq_sum_occupancy]
  rfl

theorem sum_z180K12ProjectionIndicator (A : Finset (ZMod 180)) :
    (∑ i : Fin 36, z180K12ProjectionIndicator A i) = (A.card : Int) := by
  change (∑ i : Fin 36, (z180Projection36Occupancy A i : Int)) =
    (A.card : Int)
  exact_mod_cast sum_z180Projection36Occupancy A

theorem z180K12ProjectionIndicator_nonneg
    (A : Finset (ZMod 180)) (i : Fin 36) :
    0 ≤ z180K12ProjectionIndicator A i := by
  rw [z180K12ProjectionIndicator]
  exact_mod_cast Nat.zero_le (z180Projection36Occupancy A i)

theorem z180K12ProjectionIndicator_le_one_of_injOn
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180))) (i : Fin 36) :
    z180K12ProjectionIndicator A i ≤ 1 := by
  rw [z180K12ProjectionIndicator]
  exact_mod_cast z180Projection36Occupancy_le_one_of_injOn hinj i

/-- A zero exact-order transform gives the corresponding cyclotomic divisor
of the integral mask. -/
theorem z180_cyclotomic_dvd_mask_of_transform_zero
    {A : Finset (ZMod 180)} {e : Nat} {u : ZMod 180}
    (he : e ∈ (180).divisors)
    (horder : frequencyOrder 180 u = e)
    (htransform : z180ExactOrderTransform A e = 0) :
    cyclotomic e Int ∣ maskPolynomial 180 A := by
  have henergy : exactOrderFourierEnergy A e = 0 := by
    have hid := z180RamanujanIdentity A e he
    rw [htransform] at hid
    norm_num at hid
    exact hid.symm
  have hall :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero A e).mp henergy
  have hzero := hall u horder
  simpa [CyclotomicZero, horder] using hzero

def Z180K12M6Prepared (A : Finset (ZMod 180)) : Prop :=
  ∃ k0 k1 : Int,
    (∀ i : Fin 36, 0 ≤ z180K12ProjectionIndicator A i) ∧
    (∀ i : Fin 36, z180K12ProjectionIndicator A i ≤ 1) ∧
    (
      z180K12ProjectionIndicator A 0 + z180K12ProjectionIndicator A 4 + z180K12ProjectionIndicator A 8 + z180K12ProjectionIndicator A 12 + z180K12ProjectionIndicator A 16 + z180K12ProjectionIndicator A 20 + z180K12ProjectionIndicator A 24 + z180K12ProjectionIndicator A 28 + z180K12ProjectionIndicator A 32 = 3 ∧
      z180K12ProjectionIndicator A 1 + z180K12ProjectionIndicator A 5 + z180K12ProjectionIndicator A 9 + z180K12ProjectionIndicator A 13 + z180K12ProjectionIndicator A 17 + z180K12ProjectionIndicator A 21 + z180K12ProjectionIndicator A 25 + z180K12ProjectionIndicator A 29 + z180K12ProjectionIndicator A 33 = 3 ∧
      z180K12ProjectionIndicator A 2 + z180K12ProjectionIndicator A 6 + z180K12ProjectionIndicator A 10 + z180K12ProjectionIndicator A 14 + z180K12ProjectionIndicator A 18 + z180K12ProjectionIndicator A 22 + z180K12ProjectionIndicator A 26 + z180K12ProjectionIndicator A 30 + z180K12ProjectionIndicator A 34 = 3 ∧
      z180K12ProjectionIndicator A 3 + z180K12ProjectionIndicator A 7 + z180K12ProjectionIndicator A 11 + z180K12ProjectionIndicator A 15 + z180K12ProjectionIndicator A 19 + z180K12ProjectionIndicator A 23 + z180K12ProjectionIndicator A 27 + z180K12ProjectionIndicator A 31 + z180K12ProjectionIndicator A 35 = 3) ∧
    projection36Phi6R0 (z180K12ProjectionIndicator A) = 5 * k0 ∧
    projection36Phi6R1 (z180K12ProjectionIndicator A) = 5 * k1 ∧
    (5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0)

/-- All common hypotheses for the three compact projected exclusions are
forced by the genuine cardinality-twelve `m = 6` defect data. -/
theorem z180_k12_m6_prepare
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    Z180K12M6Prepared A := by
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
  have hbmask :=
    projection36IndicatorMask_z180K12ProjectionIndicator A
  have hdiv2 :
      cyclotomic 2 Int ∣
        projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    rw [hbmask]
    exact hprojected2
  have hdiv4 :
      cyclotomic 4 Int ∣
        projection36IndicatorMask (z180K12ProjectionIndicator A) := by
    rw [hbmask]
    exact hprojected4
  have hsum :
      (∑ i : Fin 36, z180K12ProjectionIndicator A i) = 12 := by
    rw [sum_z180K12ProjectionIndicator, hcard]
    norm_num
  have hmod4 := projection36_mod4_profile
    (z180K12ProjectionIndicator A) hsum hdiv2 hdiv4
  have hmodFive :=
    cyclotomic_six_mod_five_dvd_projection36Mask_of_phi30_dvd_mask
      hdefect.1
  rw [← hbmask] at hmodFive
  obtain ⟨k0, k1, hk0, hk1⟩ :=
    projection36_phi6_five_multipliers
      (z180K12ProjectionIndicator A) hmodFive
  have hnotProjected :
      ¬ cyclotomic 6 Int ∣ z180Projection36Mask A := by
    intro hp
    exact hdefect.2.1
      ((cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 6) (by norm_num)).1 hp)
  rw [← hbmask] at hnotProjected
  have hremNe :=
    projection36_phi6_remainders_ne_of_not_dvd
      (z180K12ProjectionIndicator A) hnotProjected
  have hmulNe : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0 := by
    rcases hremNe with h0 | h1
    · left
      intro hz
      apply h0
      rw [hk0]
      exact hz
    · right
      intro hz
      apply h1
      rw [hk1]
      exact hz
  exact ⟨k0, k1,
    z180K12ProjectionIndicator_nonneg A,
    z180K12ProjectionIndicator_le_one_of_injOn hinj,
    hmod4, hk0, hk1, hmulNe⟩

#print axioms z180_cyclotomic_dvd_mask_of_transform_zero
#print axioms z180_k12_m6_prepare

end Fuglede
