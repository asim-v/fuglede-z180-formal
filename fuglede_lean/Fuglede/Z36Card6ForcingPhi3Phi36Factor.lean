import Fuglede.Z36Card6ForcingPhi36Factor12
import Mathlib.Tactic

/-! The antipodal period supplies both `Phi_4` and `Phi_12`. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private noncomputable def z36Phi4AntipodalBase
    (b : Fin 36 → Int) : Polynomial Int :=
  ∑ i : Fin 18, monomial i.val (b (i.castAdd 18))

private noncomputable def z36Phi4AntipodalQuotient : Polynomial Int :=
  X ^ 16 - X ^ 14 + X ^ 12 - X ^ 10 + X ^ 8 -
    X ^ 6 + X ^ 4 - X ^ 2 + 1

private theorem z36_cyclotomic_four_eq_int :
    cyclotomic 4 Int = X ^ 2 + 1 := by
  rw [show 4 = 2 ^ (1 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ]
  ring

private theorem z36_phi4_antipodal_factorization :
    cyclotomic 4 Int * z36Phi4AntipodalQuotient = 1 + X ^ 18 := by
  rw [z36_cyclotomic_four_eq_int]
  unfold z36Phi4AntipodalQuotient
  ring

private theorem z36_indicator_eq_antipodal_factor
    (b : Fin 36 → Int) (hanti : Z36AntipodalIndicator b) :
    projection36IndicatorMask b =
      (1 + X ^ 18) * z36Phi4AntipodalBase b := by
  have hantiFin : ∀ i : Fin 18,
      b (i.castAdd 18) = b (i.natAdd 18) := by
    intro i
    fin_cases i <;> simp_all [Z36AntipodalIndicator]
  rw [projection36IndicatorMask, Fin.sum_univ_add (a := 18) (b := 18)]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  unfold z36Phi4AntipodalBase
  rw [add_mul, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [X_pow_mul_monomial, ← hantiFin i]
  congr 2
  omega

theorem z36_antipodal_forces_phi4_phi12
    (b : Fin 36 → Int) (hanti : Z36AntipodalIndicator b) :
    cyclotomic 4 Int ∣ projection36IndicatorMask b ∧
      cyclotomic 12 Int ∣ projection36IndicatorMask b := by
  have hmask := z36_indicator_eq_antipodal_factor b hanti
  constructor
  · refine ⟨z36Phi4AntipodalQuotient * z36Phi4AntipodalBase b, ?_⟩
    calc
      projection36IndicatorMask b =
          (1 + X ^ 18) * z36Phi4AntipodalBase b := hmask
      _ = (cyclotomic 4 Int * z36Phi4AntipodalQuotient) *
          z36Phi4AntipodalBase b := by rw [z36_phi4_antipodal_factorization]
      _ = cyclotomic 4 Int *
          (z36Phi4AntipodalQuotient * z36Phi4AntipodalBase b) := by ring
  · exact z36_cyclotomic_twelve_dvd_of_antipodal b hanti

#print axioms z36_antipodal_forces_phi4_phi12

end Fuglede
