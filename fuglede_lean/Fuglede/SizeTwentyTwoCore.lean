import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Finite arithmetic for the cardinality-twenty-two argument

This module checks the elementary arithmetic endpoints in the structural
proof for spectral sets of size `22` in `ZMod 2310`.  The cyclotomic
root-sum lemma, Fourier descent, and parity-transversal argument remain
outside Lean.
-/

namespace Fuglede

/-- A size-`22` tile cannot live in the base group of order `210`. -/
theorem twenty_two_not_dvd_210 : ¬(22 : ℕ) ∣ 210 := by
  norm_num

/-- Nor can it live in the parity coset subgroup of order `1155`. -/
theorem twenty_two_not_dvd_1155 : ¬(22 : ℕ) ∣ 1155 := by
  norm_num

/-- Size `22` is compatible with the full ambient group. -/
theorem twenty_two_dvd_2310 : (22 : ℕ) ∣ 2310 := by
  norm_num

/-- The explicit complement `(2 ZMod 210) × {0}` has size `105`. -/
theorem two_hundred_ten_div_two : (210 : ℕ) / 2 = 105 := by
  norm_num

/-- The root-sum length argument reduces a nonuniform profile to the
impossible equation `11 = 5a + 7b`. -/
theorem eleven_ne_five_mul_add_seven_mul (a b : ℕ) :
    5 * a + 7 * b ≠ 11 := by
  omega

/-- Two parity classes, each containing at most three selected bases, cannot
hold the eleven points required by the level argument. -/
theorem two_three_point_parity_classes_lt_eleven
    (evenCount oddCount : ℕ)
    (heven : evenCount ≤ 3) (hodd : oddCount ≤ 3) :
    evenCount + oddCount < 11 := by
  omega

/-- An odd divisor of `210` not divisible by `3` uses only the prime factors
`5` and `7`.  These are precisely the four orders addressed by the
root-sum-length lemma. -/
theorem odd_divisor_210_not_three_dvd
    (m : ℕ) (hm : m ∣ 210) (hodd : Odd m) (hthree : ¬3 ∣ m) :
    m = 1 ∨ m = 5 ∨ m = 7 ∨ m = 35 := by
  have hmle : m ≤ 210 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> norm_num [Odd, Even] at * <;> omega

/-- If a character order `m | 210` is even, its kernel size `210 / m` is
odd.  This is the arithmetic fact that makes a character value determine
parity in the final branch. -/
theorem kernel_card_odd_of_even_divisor_210
    (m : ℕ) (hm : m ∣ 210) (heven : Even m) :
    Odd (210 / m) := by
  have hmle : m ≤ 210 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> norm_num at hm
  all_goals norm_num [Even] at heven
  all_goals try omega
  all_goals decide

end Fuglede
