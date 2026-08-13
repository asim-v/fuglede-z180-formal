import Fuglede.Z180K12M6SemanticCommon
import Fuglede.Z180K12Projection36Remainders36
import Mathlib.Tactic

/-!
# Characteristic-five descent for the remaining high zero orders at `k = 12`

If `Phi_(5m)` divides the mask, reduction modulo five makes `Phi_m`
divide the projection to `ZMod 36`.  This module records that implication
once, and exposes the integral coefficients of the monic remainder modulo
`Phi_m`.  The latter are the small integer interface used by the exact
Presburger kernels.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The `j`-th integral coefficient after reducing the 36-coordinate mask
modulo `Phi_m`. -/
noncomputable def projection36CyclotomicRemainderCoeff
    (m : Nat) (b : Fin 36 → Int) (j : Nat) : Int :=
  ((projection36IndicatorMask b) %ₘ cyclotomic m Int).coeff j

/-- Linearity reduces every symbolic remainder coefficient to the 36
concrete remainders of the monomials `X^i`. -/
theorem projection36CyclotomicRemainderCoeff_eq_sum
    (m : Nat) (b : Fin 36 → Int) (j : Nat) :
    projection36CyclotomicRemainderCoeff m b j =
      ∑ i : Fin 36,
        b i * ((X ^ i.val %ₘ cyclotomic m Int).coeff j) := by
  classical
  have hmonomial (i : Fin 36) :
      monomial i.val (b i) = b i • (X : Polynomial Int) ^ i.val := by
    rw [zsmul_eq_mul]
    have hC : ((b i : Int) : Polynomial Int) = C (b i) :=
      (C_eq_intCast (b i)).symm
    rw [hC, C_mul_X_pow_eq_monomial]
  rw [projection36CyclotomicRemainderCoeff,
    projection36IndicatorMask]
  change
    ((modByMonicHom (cyclotomic m Int))
      (∑ i : Fin 36, monomial i.val (b i))).coeff j = _
  rw [map_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hmonomial i]
  calc
    ((modByMonicHom (cyclotomic m Int))
        (b i • (X : Polynomial Int) ^ i.val)).coeff j =
        (b i • (modByMonicHom (cyclotomic m Int))
          ((X : Polynomial Int) ^ i.val)).coeff j := by
      rw [map_zsmul]
    _ = b i •
        ((modByMonicHom (cyclotomic m Int))
          ((X : Polynomial Int) ^ i.val)).coeff j := by
      change (lcoeff Int j)
          (b i • (modByMonicHom (cyclotomic m Int))
            ((X : Polynomial Int) ^ i.val)) =
        b i • (lcoeff Int j)
          ((modByMonicHom (cyclotomic m Int))
            ((X : Polynomial Int) ^ i.val))
      rw [map_zsmul]
    _ = b i * ((X ^ i.val %ₘ cyclotomic m Int).coeff j) := by
      rw [Int.zsmul_eq_mul]
      rfl

/-- Generic form of the characteristic-five projection argument. -/
theorem cyclotomic_mod_five_dvd_projection36Mask_of_five_mul_dvd_mask
    {A : Finset (ZMod 180)} {m : Nat}
    (hm5 : ¬ 5 ∣ m) (hm36 : m ∣ 36)
    (hhigh : cyclotomic (5 * m) Int ∣ maskPolynomial 180 A) :
    cyclotomic m (ZMod 5) ∣
      (z180Projection36Mask A).map (Int.castRingHom (ZMod 5)) := by
  have hmapped : cyclotomic m (ZMod 5) ∣
      (maskPolynomial 180 A).map (Int.castRingHom (ZMod 5)) :=
    cyclotomic_mod_five_dvd_of_five_mul_index_dvd hm5 hhigh
  have hraw := Polynomial.map_dvd (Int.castRingHom (ZMod 5))
    (X_pow_36_sub_one_dvd_mask_sub_projection A)
  have hdiffMapped :
      (X ^ 36 - 1 : Polynomial (ZMod 5)) ∣
        (maskPolynomial 180 A).map (Int.castRingHom (ZMod 5)) -
          (z180Projection36Mask A).map (Int.castRingHom (ZMod 5)) := by
    simpa using hraw
  have hcyclo : cyclotomic m (ZMod 5) ∣
      (X ^ 36 - 1 : Polynomial (ZMod 5)) :=
    (cyclotomic.dvd_X_pow_sub_one m (ZMod 5)).trans
      (dvd_pow_sub_one_of_dvd hm36)
  have hdiff := hcyclo.trans hdiffMapped
  have hsub := dvd_sub hmapped hdiff
  simpa using hsub

/-- Indicator-mask spelling of the preceding projection result. -/
theorem cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
    {A : Finset (ZMod 180)} {m : Nat}
    (hm5 : ¬ 5 ∣ m) (hm36 : m ∣ 36)
    (hhigh : cyclotomic (5 * m) Int ∣ maskPolynomial 180 A) :
    cyclotomic m (ZMod 5) ∣
      (projection36IndicatorMask
        (z180K12ProjectionIndicator A)).map
          (Int.castRingHom (ZMod 5)) := by
  rw [projection36IndicatorMask_z180K12ProjectionIndicator]
  exact cyclotomic_mod_five_dvd_projection36Mask_of_five_mul_dvd_mask
    hm5 hm36 hhigh

/-- Divisibility of the mapped mask annihilates every mapped coefficient of
the integral monic remainder.  This avoids repeating polynomial long
division separately in characteristic five. -/
theorem projection36CyclotomicRemainderCoeff_mod_five_eq_zero
    {m : Nat} (b : Fin 36 → Int)
    (hdiv : cyclotomic m (ZMod 5) ∣
      (projection36IndicatorMask b).map
        (Int.castRingHom (ZMod 5))) (j : Nat) :
    (projection36CyclotomicRemainderCoeff m b j : ZMod 5) = 0 := by
  have hmonic : (cyclotomic m Int).Monic := cyclotomic.monic m Int
  have hmappedMonic : (cyclotomic m (ZMod 5)).Monic :=
    cyclotomic.monic m (ZMod 5)
  have hmappedZero :
      (projection36IndicatorMask b).map
          (Int.castRingHom (ZMod 5)) %ₘ cyclotomic m (ZMod 5) = 0 :=
    (modByMonic_eq_zero_iff_dvd hmappedMonic).2 hdiv
  have hmap := map_modByMonic (p := projection36IndicatorMask b)
    (Int.castRingHom (ZMod 5)) hmonic
  rw [map_cyclotomic] at hmap
  have hcoeff := congrArg (fun P : Polynomial (ZMod 5) ↦ P.coeff j)
    (hmap.trans hmappedZero)
  simpa [projection36CyclotomicRemainderCoeff] using hcoeff

/-- Integer-multiple form consumed by Presburger arithmetic. -/
theorem projection36CyclotomicRemainderCoeff_eq_five_mul
    {m : Nat} (b : Fin 36 → Int)
    (hdiv : cyclotomic m (ZMod 5) ∣
      (projection36IndicatorMask b).map
        (Int.castRingHom (ZMod 5))) (j : Nat) :
    ∃ k : Int, projection36CyclotomicRemainderCoeff m b j = 5 * k := by
  have hz := projection36CyclotomicRemainderCoeff_mod_five_eq_zero
    b hdiv j
  have hdvd : (5 : Int) ∣ projection36CyclotomicRemainderCoeff m b j := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (projection36CyclotomicRemainderCoeff m b j) 5).mp hz
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k, by simpa [mul_comm] using hk⟩

/-- Vanishing of every coefficient below the cyclotomic degree reconstructs
ordinary integral divisibility. -/
theorem cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero
    {m : Nat} (b : Fin 36 → Int)
    (hz : ∀ j < Nat.totient m,
      projection36CyclotomicRemainderCoeff m b j = 0) :
    cyclotomic m Int ∣ projection36IndicatorMask b := by
  have hmonic : (cyclotomic m Int).Monic := cyclotomic.monic m Int
  apply (modByMonic_eq_zero_iff_dvd hmonic).1
  apply Polynomial.ext
  intro j
  by_cases hj : j < Nat.totient m
  · simpa [projection36CyclotomicRemainderCoeff] using hz j hj
  · have hdegree :
        (projection36IndicatorMask b %ₘ cyclotomic m Int).degree <
          (Nat.totient m : Nat) := by
      simpa [degree_cyclotomic] using
        degree_modByMonic_lt (projection36IndicatorMask b) hmonic
    have hcoeff :
        (projection36IndicatorMask b %ₘ cyclotomic m Int).coeff j = 0 := by
      apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hdegree (by exact_mod_cast Nat.le_of_not_gt hj)
    simp [hcoeff]

#print axioms cyclotomic_mod_five_dvd_projection36Mask_of_five_mul_dvd_mask
#print axioms projection36CyclotomicRemainderCoeff_mod_five_eq_zero
#print axioms projection36CyclotomicRemainderCoeff_eq_five_mul
#print axioms cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero

end Fuglede
