import Mathlib.Tactic

/-! # Pairwise Presburger kernel for the order-sixty branch -/

namespace Fuglede

namespace Z180K12HighOrder

set_option maxHeartbeats 0
set_option linter.unusedVariables false

private theorem order60_five_bounded_six_cases_pair
    (p k : Int) (hlo : -6 ≤ p) (hhi : p ≤ 6)
    (hfive : p = 5 * k) :
    p = -5 ∨ p = 0 ∨ p = 5 := by
  omega

private theorem order60_five_cases_eq_of_sub_three_pair
    (p q s : Int)
    (hp : p = -5 ∨ p = 0 ∨ p = 5)
    (hq : q = -5 ∨ q = 0 ∨ q = 5)
    (hsub : p - q = 3 * s) :
    p = q := by
  rcases hp with hp | hp | hp <;>
    rcases hq with hq | hq | hq <;> omega

private theorem order60_five_equal_sum_bounded_zero_pair
    (p q : Int)
    (hp : p = -5 ∨ p = 0 ∨ p = 5)
    (hq : q = -5 ∨ q = 0 ∨ q = 5)
    (heq : p = q) (hlo : -6 ≤ p + q) (hhi : p + q ≤ 6) :
    p = 0 ∧ q = 0 := by
  rcases hp with hp | hp | hp <;>
    rcases hq with hq | hq | hq <;> omega

/-- A pair of three-point residue fibres cannot support nonzero
five-multiples of the two coupled `Phi_12` remainders. -/
theorem order60_pair_remainders_zero
    (a b c d e f t u : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hsum0 : a + b + c = 3)
    (hsum1 : d + e + f = 3)
    (hr0 : a - b - e + f = 5 * t)
    (hr1 : d + b - c - f = 5 * u) :
    a - b - e + f = 0 ∧ d + b - c - f = 0 := by
  let p : Int := a - b - e + f
  let q : Int := d + b - c - f
  have hpLo : -6 ≤ p := by
    dsimp only [p]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  have hpHi : p ≤ 6 := by
    dsimp only [p]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  have hqLo : -6 ≤ q := by
    dsimp only [q]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  have hqHi : q ≤ 6 := by
    dsimp only [q]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  have hp5 : p = 5 * t := by simpa only [p] using hr0
  have hq5 : q = 5 * u := by simpa only [q] using hr1
  have hpCases := order60_five_bounded_six_cases_pair p t hpLo hpHi hp5
  have hqCases := order60_five_bounded_six_cases_pair q u hqLo hqHi hq5
  have hpqThree : p - q = 3 * (3 - b - d - e) := by
    dsimp only [p, q]
    linear_combination hsum0 + 2 * hsum1
  have hpq : p = q := order60_five_cases_eq_of_sub_three_pair
    p q (3 - b - d - e) hpCases hqCases hpqThree
  have hpqLo : -6 ≤ p + q := by
    dsimp only [p, q]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  have hpqHi : p + q ≤ 6 := by
    dsimp only [p, q]
    linarith only [ha, hb, hc, hd, he, hf, hsum0, hsum1]
  simpa only [p, q] using
    order60_five_equal_sum_bounded_zero_pair p q
      hpCases hqCases hpq hpqLo hpqHi

#print axioms order60_pair_remainders_zero

end Z180K12HighOrder

end Fuglede
