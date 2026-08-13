import Fuglede.Z36Card6ForcingPhi36Predicates
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z180K12Projection36Remainders18
import Mathlib.Tactic

/-! Direct `Phi_18` factor supplied by three-cycle 36-bit indicators. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private noncomputable def z36ThreeCycleBase (b : Fin 36 → Int) : Polynomial Int :=
  ∑ i : Fin 12, monomial i.val (b (i.castAdd 24))

private noncomputable def z36Phi18CycleQuotient : Polynomial Int :=
  X ^ 18 + X ^ 15 - X ^ 9 + X ^ 3 + 1

private theorem z36_phi18_cycle_factorization :
    cyclotomic 18 Int * z36Phi18CycleQuotient =
      1 + X ^ 12 + X ^ 24 := by
  rw [cyclotomic_eighteen_eq_int]
  unfold z36Phi18CycleQuotient
  ring

theorem z36_cyclotomic_eighteen_dvd_of_three_cycle
    (b : Fin 36 → Int) (hcycle : Z36ThreeCycleIndicator b) :
    cyclotomic 18 Int ∣ projection36IndicatorMask b := by
  have hmiddleFin : ∀ i : Fin 12,
      b (i.castAdd 24) = b ((i.castAdd 12).natAdd 12) := by
    intro i
    fin_cases i <;> simp_all [Z36ThreeCycleIndicator]
  have hhighFin : ∀ i : Fin 12,
      b (i.castAdd 24) = b ((i.natAdd 12).natAdd 12) := by
    intro i
    fin_cases i <;> simp_all [Z36ThreeCycleIndicator]
  have hmask : projection36IndicatorMask b =
      (1 + X ^ 12 + X ^ 24) * z36ThreeCycleBase b := by
    have hmiddle :
        (∑ i : Fin 12, monomial (12 + i.val)
          (b ((i.castAdd 12).natAdd 12))) =
          X ^ 12 * z36ThreeCycleBase b := by
      unfold z36ThreeCycleBase
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [X_pow_mul_monomial, ← hmiddleFin i]
      congr 2
      omega
    have hhigh :
        (∑ i : Fin 12, monomial (12 + (12 + i.val))
          (b ((i.natAdd 12).natAdd 12))) =
          X ^ 24 * z36ThreeCycleBase b := by
      unfold z36ThreeCycleBase
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [X_pow_mul_monomial, ← hhighFin i]
      congr 2
      omega
    rw [projection36IndicatorMask,
      Fin.sum_univ_add (a := 12) (b := 24),
      Fin.sum_univ_add (a := 12) (b := 12)]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    rw [hmiddle, hhigh]
    change z36ThreeCycleBase b +
      (X ^ 12 * z36ThreeCycleBase b + X ^ 24 * z36ThreeCycleBase b) = _
    ring
  refine ⟨z36Phi18CycleQuotient * z36ThreeCycleBase b, ?_⟩
  calc
    projection36IndicatorMask b =
        (1 + X ^ 12 + X ^ 24) * z36ThreeCycleBase b := hmask
    _ = (cyclotomic 18 Int * z36Phi18CycleQuotient) *
        z36ThreeCycleBase b := by rw [z36_phi18_cycle_factorization]
    _ = cyclotomic 18 Int *
        (z36Phi18CycleQuotient * z36ThreeCycleBase b) := by ring

#print axioms z36_cyclotomic_eighteen_dvd_of_three_cycle

end Fuglede
