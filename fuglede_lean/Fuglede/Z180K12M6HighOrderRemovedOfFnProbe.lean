import Fuglede.Z180K12M6HighOrderModFive
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic

/-! # Isolated `ofFn` probe for the high-order remainder-removal identity -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private noncomputable def projection36RemainderRemovedProbe
    (m : Nat) (b : Fin 36 → Int) : Fin 36 → Int :=
  fun i ↦ b i - projection36CyclotomicRemainderCoeff m b i.val

private theorem projection36IndicatorMask_eq_ofFn_probe
    (b : Fin 36 → Int) :
    projection36IndicatorMask b = Polynomial.ofFn 36 b := by
  rw [projection36IndicatorMask, Polynomial.ofFn_eq_sum_monomial]

theorem projection36IndicatorMask_remainderRemoved_ofFn_probe
    (m : Nat) (b : Fin 36 → Int) (htot : Nat.totient m ≤ 36) :
    projection36IndicatorMask (projection36RemainderRemovedProbe m b) =
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
  unfold projection36RemainderRemovedProbe
  unfold projection36CyclotomicRemainderCoeff
  rw [projection36IndicatorMask_eq_ofFn_probe,
    projection36IndicatorMask_eq_ofFn_probe]
  change Polynomial.ofFn 36 (fun i ↦ b i - R.coeff i.val) =
    Polynomial.ofFn 36 b - R
  rw [show (fun i : Fin 36 ↦ b i - R.coeff i.val) =
      b - (fun i : Fin 36 ↦ R.coeff i.val) by rfl]
  rw [map_sub, hRfn]

#print axioms projection36IndicatorMask_remainderRemoved_ofFn_probe

end Fuglede
