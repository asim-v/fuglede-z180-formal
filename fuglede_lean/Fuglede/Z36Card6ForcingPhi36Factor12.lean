import Fuglede.Z36Card6ForcingPhi36Predicates
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-! Direct `Phi_12` factor supplied by antipodal 36-bit indicators. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private noncomputable def z36AntipodalBase (b : Fin 36 → Int) : Polynomial Int :=
  ∑ i : Fin 18, monomial i.val (b (i.castAdd 18))

private noncomputable def z36Phi12PairQuotient : Polynomial Int :=
  X ^ 14 + X ^ 12 - X ^ 8 - X ^ 6 + X ^ 2 + 1

private theorem z36_phi12_pair_factorization :
    cyclotomic 12 Int * z36Phi12PairQuotient = 1 + X ^ 18 := by
  rw [cyclotomic_twelve_eq_int]
  unfold z36Phi12PairQuotient
  ring

theorem z36_cyclotomic_twelve_dvd_of_antipodal
    (b : Fin 36 → Int) (hanti : Z36AntipodalIndicator b) :
    cyclotomic 12 Int ∣ projection36IndicatorMask b := by
  have hantiFin : ∀ i : Fin 18,
      b (i.castAdd 18) = b (i.natAdd 18) := by
    intro i
    fin_cases i <;> simp_all [Z36AntipodalIndicator]
  have hmask : projection36IndicatorMask b =
      (1 + X ^ 18) * z36AntipodalBase b := by
    rw [projection36IndicatorMask, Fin.sum_univ_add (a := 18) (b := 18)]
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    unfold z36AntipodalBase
    rw [add_mul, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [X_pow_mul_monomial, ← hantiFin i]
    congr 2
    omega
  refine ⟨z36Phi12PairQuotient * z36AntipodalBase b, ?_⟩
  calc
    projection36IndicatorMask b =
        (1 + X ^ 18) * z36AntipodalBase b := hmask
    _ = (cyclotomic 12 Int * z36Phi12PairQuotient) *
        z36AntipodalBase b := by rw [z36_phi12_pair_factorization]
    _ = cyclotomic 12 Int *
        (z36Phi12PairQuotient * z36AntipodalBase b) := by ring

#print axioms z36_cyclotomic_twelve_dvd_of_antipodal

end Fuglede
