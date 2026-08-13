import Fuglede.Z180K12M6Order60PairKernel
import Mathlib.Tactic

/-! # Final Presburger assembly for the order-sixty branch -/

namespace Fuglede

namespace Z180K12HighOrder

set_option maxHeartbeats 0
set_option linter.unusedVariables false

private theorem order60_even_five_bounded_cases_final
    (p k a : Int)
    (hlo : -12 ≤ p) (hhi : p ≤ 12)
    (hfive : p = 5 * k) (heven : p = 2 * a) :
    p = -10 ∨ p = 0 ∨ p = 10 := by
  omega

private theorem order60_cases_eq_of_sub_six_final
    (p q s : Int)
    (hp : p = -10 ∨ p = 0 ∨ p = 10)
    (hq : q = -10 ∨ q = 0 ∨ q = 10)
    (hsub : p - q = 6 * s) :
    p = q := by
  rcases hp with hp | hp | hp <;>
    rcases hq with hq | hq | hq <;> omega

private theorem order60_even_equal_sum_bounded_zero_final
    (p q : Int)
    (hp : p = -10 ∨ p = 0 ∨ p = 10)
    (hq : q = -10 ∨ q = 0 ∨ q = 10)
    (heq : p = q) (hlo : -12 ≤ p + q) (hhi : p + q ≤ 12) :
    p = 0 ∧ q = 0 := by
  rcases hp with hp | hp | hp <;>
    rcases hq with hq | hq | hq <;> omega

theorem z180_k12_m6_order60_count_impossible
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Int)
    (k0 k1 t0 t1 t2 t3 : Int)
    (hc0lo : 0 ≤ c0) (hc0hi : c0 ≤ 3)
    (hc1lo : 0 ≤ c1) (hc1hi : c1 ≤ 3)
    (hc2lo : 0 ≤ c2) (hc2hi : c2 ≤ 3)
    (hc3lo : 0 ≤ c3) (hc3hi : c3 ≤ 3)
    (hc4lo : 0 ≤ c4) (hc4hi : c4 ≤ 3)
    (hc5lo : 0 ≤ c5) (hc5hi : c5 ≤ 3)
    (hc6lo : 0 ≤ c6) (hc6hi : c6 ≤ 3)
    (hc7lo : 0 ≤ c7) (hc7hi : c7 ≤ 3)
    (hc8lo : 0 ≤ c8) (hc8hi : c8 ≤ 3)
    (hc9lo : 0 ≤ c9) (hc9hi : c9 ≤ 3)
    (hc10lo : 0 ≤ c10) (hc10hi : c10 ≤ 3)
    (hc11lo : 0 ≤ c11) (hc11hi : c11 ≤ 3)
    (hmod4_0 : c0 + c4 + c8 = 3)
    (hmod4_1 : c1 + c5 + c9 = 3)
    (hmod4_2 : c2 + c6 + c10 = 3)
    (hmod4_3 : c3 + c7 + c11 = 3)
    (hphi12_0 : c0 - c4 - c6 + c10 = 5 * t0)
    (hphi12_1 : c1 - c5 - c7 + c11 = 5 * t1)
    (hphi12_2 : c2 + c4 - c8 - c10 = 5 * t2)
    (hphi12_3 : c3 + c5 - c9 - c11 = 5 * t3)
    (hphi6_0 : c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 = 5 * k0)
    (hphi6_1 : c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 = 5 * k1)
    (hphi6_ne :
      c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 ≠ 0 ∨
      c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 ≠ 0) :
    False := by
  obtain ⟨h12_0, h12_2⟩ := order60_pair_remainders_zero
    c0 c4 c8 c2 c6 c10 t0 t2
    hc0lo hc4lo hc8lo hc2lo hc6lo hc10lo
    hmod4_0 hmod4_2 hphi12_0 hphi12_2
  obtain ⟨h12_1, h12_3⟩ := order60_pair_remainders_zero
    c1 c5 c9 c3 c7 c11 t1 t3
    hc1lo hc5lo hc9lo hc3lo hc7lo hc11lo
    hmod4_1 hmod4_3 hphi12_1 hphi12_3
  let p : Int := c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11
  let q : Int := c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11
  have hp5 : p = 5 * k0 := by simpa only [p] using hphi6_0
  have hq5 : q = 5 * k1 := by simpa only [q] using hphi6_1
  have hpLo : -12 ≤ p := by
    dsimp only [p]
    linarith only [hc0lo, hc2hi, hc3hi, hc5lo,
      hc6lo, hc8hi, hc9hi, hc11lo]
  have hpHi : p ≤ 12 := by
    dsimp only [p]
    linarith only [hc0hi, hc2lo, hc3lo, hc5hi,
      hc6hi, hc8lo, hc9lo, hc11hi]
  have hqLo : -12 ≤ q := by
    dsimp only [q]
    linarith only [hc1lo, hc2lo, hc4hi, hc5hi,
      hc7lo, hc8lo, hc10hi, hc11hi]
  have hqHi : q ≤ 12 := by
    dsimp only [q]
    linarith only [hc1hi, hc2hi, hc4lo, hc5lo,
      hc7hi, hc8hi, hc10lo, hc11lo]
  have hpEven : p = 2 * (c6 - c2 + c11 - c3) := by
    dsimp only [p]
    linear_combination h12_0 + h12_2 + h12_3
  have hqEven : q = 2 * (c8 - c4 + c7 - c11) := by
    dsimp only [q]
    linear_combination h12_2 + h12_1
  have hpCases := order60_even_five_bounded_cases_final
    p k0 (c6 - c2 + c11 - c3) hpLo hpHi hp5 hpEven
  have hqCases := order60_even_five_bounded_cases_final
    q k1 (c8 - c4 + c7 - c11) hqLo hqHi hq5 hqEven
  have hpqSix :
      p - q = 6 * (3 - c1 - c2 - c3 + c5 - c11) := by
    dsimp only [p, q]
    linear_combination
      2 * hmod4_2 + 4 * hmod4_3 + h12_0 +
        5 * h12_1 + 2 * h12_2 + h12_3
  have hpq : p = q := order60_cases_eq_of_sub_six_final
    p q (3 - c1 - c2 - c3 + c5 - c11) hpCases hqCases hpqSix
  have hpqLo : -12 ≤ p + q := by
    dsimp only [p, q]
    linarith only [hc0lo, hc1lo, hc3hi, hc4hi,
      hc6lo, hc7lo, hc9hi, hc10hi]
  have hpqHi : p + q ≤ 12 := by
    dsimp only [p, q]
    linarith only [hc0hi, hc1hi, hc3lo, hc4lo,
      hc6hi, hc7hi, hc9lo, hc10lo]
  obtain ⟨hpZero, hqZero⟩ := order60_even_equal_sum_bounded_zero_final
    p q hpCases hqCases hpq hpqLo hpqHi
  change p ≠ 0 ∨ q ≠ 0 at hphi6_ne
  exact hphi6_ne.elim (fun h ↦ h hpZero) (fun h ↦ h hqZero)

#print axioms z180_k12_m6_order60_count_impossible

end Z180K12HighOrder

end Fuglede
