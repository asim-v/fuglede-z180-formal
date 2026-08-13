import Fuglede.Z180K12M6HighOrderModFive
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic

/-!
# Removing the integral cyclotomic remainder

This generic bridge replaces explicit long division in the high-order
`k = 12` adapters.  Subtracting the first 36 coefficients of the monic
remainder from the projected vector produces an honest integral
cyclotomic multiple.  Characteristic-five divisibility says that every
subtracted coefficient is a multiple of five.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def projection36RemainderRemoved
    (m : Nat) (b : Fin 36 → Int) : Fin 36 → Int :=
  fun i ↦ b i - projection36CyclotomicRemainderCoeff m b i.val

/-- Coefficients of the monic remainder vanish from the cyclotomic degree
onwards. -/
theorem projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    {m j : Nat} (b : Fin 36 → Int) (hj : Nat.totient m ≤ j) :
    projection36CyclotomicRemainderCoeff m b j = 0 := by
  apply coeff_eq_zero_of_degree_lt
  have hdegree :
      (projection36IndicatorMask b %ₘ cyclotomic m Int).degree <
        (Nat.totient m : Nat) := by
    simpa [degree_cyclotomic] using
      degree_modByMonic_lt (projection36IndicatorMask b)
        (cyclotomic.monic m Int)
  exact lt_of_lt_of_le hdegree (by exact_mod_cast hj)

private theorem projection36IndicatorMask_eq_ofFn
    (b : Fin 36 → Int) :
    projection36IndicatorMask b = Polynomial.ofFn 36 b := by
  rw [projection36IndicatorMask, Polynomial.ofFn_eq_sum_monomial]

/-- The removed vector represents the mask minus its monic remainder.
The totient bound only ensures that the remainder fits into 36
coordinates. -/
theorem projection36IndicatorMask_remainderRemoved
    (m : Nat) (b : Fin 36 → Int) (htot : Nat.totient m ≤ 36) :
    projection36IndicatorMask (projection36RemainderRemoved m b) =
      projection36IndicatorMask b -
        projection36IndicatorMask b %ₘ cyclotomic m Int := by
  classical
  let R := Polynomial.ofFn 36 b %ₘ cyclotomic m Int
  have hdegree : R.degree < (Nat.totient m : Nat) := by
    dsimp only [R]
    simpa [degree_cyclotomic] using
      degree_modByMonic_lt (Polynomial.ofFn 36 b)
        (cyclotomic.monic m Int)
  have hdegree36 : R.degree < (36 : Nat) := by
    exact lt_of_lt_of_le hdegree (by exact_mod_cast htot)
  have hnatDegree : R.natDegree < 36 := by
    by_cases hR : R = 0
    · simp [hR]
    · exact (natDegree_lt_iff_degree_lt hR).2 hdegree36
  have hRfn : Polynomial.ofFn 36 (fun i : Fin 36 ↦ R.coeff i.val) = R := by
    have hfun : (fun i : Fin 36 ↦ R.coeff i.val) =
        Polynomial.toFn 36 R := by
      funext i
      rfl
    rw [hfun]
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hnatDegree
  unfold projection36RemainderRemoved
  unfold projection36CyclotomicRemainderCoeff
  rw [projection36IndicatorMask_eq_ofFn,
    projection36IndicatorMask_eq_ofFn]
  change Polynomial.ofFn 36 (fun i ↦ b i - R.coeff i.val) =
    Polynomial.ofFn 36 b - R
  rw [show (fun i : Fin 36 ↦ b i - R.coeff i.val) =
      b - (fun i : Fin 36 ↦ R.coeff i.val) by rfl]
  rw [map_sub, hRfn]

/-- The remainder-removed mask is integrally divisible by the chosen
cyclotomic polynomial. -/
theorem cyclotomic_dvd_projection36RemainderRemoved
    (m : Nat) (b : Fin 36 → Int) (htot : Nat.totient m ≤ 36) :
    cyclotomic m Int ∣
      projection36IndicatorMask (projection36RemainderRemoved m b) := by
  rw [projection36IndicatorMask_remainderRemoved m b htot]
  have h := dvd_modByMonic_sub
    (projection36IndicatorMask b) (cyclotomic m Int)
  have hneg : cyclotomic m Int ∣
      -((projection36IndicatorMask b %ₘ cyclotomic m Int) -
        projection36IndicatorMask b) := dvd_neg.mpr h
  convert hneg using 1 <;> ring

/-- Every removed coordinate differs from the original one by a multiple
of five under mapped cyclotomic divisibility. -/
theorem projection36RemainderRemoved_eq_sub_five_mul
    {m : Nat} (b : Fin 36 → Int)
    (hdiv : cyclotomic m (ZMod 5) ∣
      (projection36IndicatorMask b).map
        (Int.castRingHom (ZMod 5))) (i : Fin 36) :
    ∃ k : Int, projection36RemainderRemoved m b i = b i - 5 * k := by
  obtain ⟨k, hk⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv i.val
  exact ⟨k, by simp [projection36RemainderRemoved, hk]⟩

#print axioms cyclotomic_dvd_projection36RemainderRemoved
#print axioms projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
#print axioms projection36RemainderRemoved_eq_sub_five_mul

end Fuglede
